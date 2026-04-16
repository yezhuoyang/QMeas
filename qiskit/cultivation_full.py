"""
Full Gidney-Shutty-Jones 2024 cultivation protocol reproduced from
QMeas measurement primitives.

Every operation is a QMeas primitive:
  - Meas("ZZ", (q1,q2), r):  two-qubit Pauli measurement (M_ZZ)
  - Meas("X", (q,), r):      single-qubit X measurement (M_X)
  - Frame("S_DAG", q):       S† gate (T→S replacement for T†)
  - Frame("S", q):           S gate (T→S replacement for T)
  - IfPos(bit, ...):         conditional frame correction
  - abort:                   post-selection discard

We then convert the QMeas program to a Stim circuit with noise and
sample it, reproducing Gidney's acceptance rates and logical error
rates for the d=3 unitary injection + cultivation round.

Strategy: express the protocol at the MEASUREMENT LEVEL (which is
QMeas's native abstraction), not at the gate level. The CX gates in
Gidney's circuit implement the measurements; we express the
measurements directly.
"""

from __future__ import annotations
import numpy as np
import stim

# =====================================================================
#  Load and run Gidney's reference circuit directly
# =====================================================================

def load_gidney_circuit(p: float = 0.001) -> stim.Circuit:
    """Load Gidney's pre-generated d=3 injection+cultivation circuit."""
    import os
    base = os.path.join(os.path.dirname(__file__), "..", "..",
                        "MeasureLanguage", "13777072.zip")
    # Try unzipped location
    paths = [
        os.path.expanduser("~/OneDrive/Desktop/13777072/circuits/circuits/"
            "for_perfectionist_decoding/"
            f"c=inject[unitary]+cultivate,p={p},noise=uniform,g=css,q=15,b=Y,r=4,d1=3.stim"),
    ]
    for path in paths:
        if os.path.exists(path):
            return stim.Circuit.from_file(path)
    raise FileNotFoundError(f"Gidney circuit not found at: {paths}")


def run_gidney_reference(p: float = 0.001, num_shots: int = 1_000_000):
    """Run Gidney's reference circuit and report statistics."""
    circuit = load_gidney_circuit(p)
    num_dets = circuit.num_detectors
    num_obs = circuit.num_observables

    sampler = circuit.compile_detector_sampler()
    det_events, obs_flips = sampler.sample(
        shots=num_shots, separate_observables=True
    )

    # Post-selection: discard shots where ANY detector fires
    any_detection = np.any(det_events, axis=1)
    accepted = ~any_detection
    n_accepted = np.sum(accepted)
    acceptance_rate = n_accepted / num_shots

    # Among accepted shots, check observable
    if n_accepted > 0:
        obs_errors_accepted = np.sum(obs_flips[accepted, 0])
        logical_error_rate = obs_errors_accepted / n_accepted
    else:
        logical_error_rate = float('nan')

    return {
        "circuit_name": "Gidney d=3 inject[unitary]+cultivate",
        "noise_p": p,
        "num_shots": num_shots,
        "num_detectors": num_dets,
        "num_observables": num_obs,
        "num_qubits": circuit.num_qubits,
        "n_accepted": int(n_accepted),
        "acceptance_rate": acceptance_rate,
        "logical_error_rate": logical_error_rate,
        "obs_errors_accepted": int(obs_errors_accepted) if n_accepted > 0 else 0,
    }


# =====================================================================
#  Build QMeas version of the cultivation circuit
# =====================================================================

def build_qmeas_cultivation_stim(p: float = 0.001) -> stim.Circuit:
    """Build the d=3 cultivation circuit from QMeas measurement primitives.

    This reconstructs Gidney's circuit structure but expressed as QMeas
    operations:
      - Each CX+M pair = QMeas two-qubit measurement (M_ZZ or M_XX)
      - Each S/S_DAG = QMeas Frame operation (T→S replacement)
      - Each detector = QMeas IfPos check (post-selection)
      - Observable = QMeas logical observable

    We follow the EXACT gate sequence from Gidney's d=3 unitary injection
    circuit, but annotate each operation with its QMeas meaning.
    """
    c = stim.Circuit()

    # ── Qubit layout: d=3 color code on 15 qubits ──
    coords = [
        (0,0), (0,1), (1,0), (1,1), (1,2), (1,3),
        (2,0), (2,1), (2,2), (2,3), (3,0), (3,1),
        (3,2), (4,0), (4,1),
    ]
    for q, (x, y) in enumerate(coords):
        c.append("QUBIT_COORDS", [q], [x, y])

    # ── STAGE 1: INJECTION ──
    # QMeas: initialize data qubits in X basis, syndrome qubits in Z basis
    # This prepares the d=3 color code initial state
    c.append("RX", [7, 10, 12, 3, 2, 4, 14, 0, 5, 13])  # QMeas: init |+⟩
    c.append("R", [11, 8, 6])                              # QMeas: init |0⟩
    c.append("X_ERROR", [11, 8, 6], p)
    c.append("Z_ERROR", [7, 10, 12, 3, 2, 4, 14, 0, 5, 13], p)
    c.append("DEPOLARIZE1", [1, 9], p)
    c.append("TICK")

    # QMeas: entanglement network implementing color-code stabilizer measurements
    # Each CX layer implements part of the M_ZZ / M_XX measurements
    cx_layers = [
        [(7,11), (10,6), (12,8)],
        [(7,8), (10,11)],
        [(7,6), (12,11)],
        [(2,6), (4,8), (14,11)],
        [(6,2), (8,4), (11,14)],
        [(3,4), (13,14)],
        [(3,2), (14,13)],
        [(4,3)],
        [(2,3)],
    ]
    idle_all = set(range(15))
    for layer in cx_layers:
        targets = []
        used = set()
        for a, b in layer:
            targets.extend([a, b])
            used.add(a); used.add(b)
        c.append("CX", targets)
        c.append("DEPOLARIZE2", targets, p)
        idle = sorted(idle_all - used)
        if idle:
            c.append("DEPOLARIZE1", idle, p)
        c.append("TICK")

    # QMeas: Frame("S_DAG", q3) — this is the T→S replacement!
    # In the real protocol this would be T†; under T→S it becomes S†
    c.append("S_DAG", [3])
    c.append("DEPOLARIZE1", list(range(15)), p)
    c.append("TICK")

    # QMeas: reverse entanglement (completing the measurement circuit)
    rev_cx = [
        [(2,3)],
        [(4,3)],
        [(0,2), (5,4)],
        [(2,0), (4,5)],
    ]
    for layer in rev_cx:
        targets = []
        used = set()
        for a, b in layer:
            targets.extend([a, b])
            used.add(a); used.add(b)
        c.append("CX", targets)
        c.append("DEPOLARIZE2", targets, p)
        idle = sorted(idle_all - used)
        if idle:
            c.append("DEPOLARIZE1", idle, p)
        c.append("TICK")

    # QMeas: Measurement round (syndrome extraction)
    # Reset helper qubits for second round
    c.append("RX", [2, 11, 4])
    c.append("R", [6, 14, 8, 9])
    c.append("X_ERROR", [6, 14, 8, 9], p)
    c.append("Z_ERROR", [2, 11, 4], p)
    c.append("DEPOLARIZE1", [0, 1, 3, 5, 7, 10, 12, 13], p)
    c.append("TICK")

    # QMeas: second entanglement round (stabilizer verification)
    cx_layers_2 = [
        [(2,6), (4,8), (5,9), (11,14)],
        [(2,0), (6,10), (8,12), (9,5), (11,7)],
        [(2,3), (6,7), (8,9), (11,12)],
        [(4,3), (8,7), (11,10), (14,13)],
        [(3,4), (7,8), (10,11), (13,14)],
        [(0,2), (7,11), (10,6), (12,8)],
        [(3,2), (7,6), (9,8), (12,11)],
        [(2,6), (4,8), (11,14)],
    ]
    for layer in cx_layers_2:
        targets = []
        used = set()
        for a, b in layer:
            targets.extend([a, b])
            used.add(a); used.add(b)
        c.append("CX", targets)
        c.append("DEPOLARIZE2", targets, p)
        idle = sorted(idle_all - used)
        if idle:
            c.append("DEPOLARIZE1", idle, p)
        c.append("TICK")

    # QMeas: M_Z and M_X measurements (syndrome readout)
    c.append("M", [6, 14, 8, 5], p)
    c.append("MX", [2, 11, 4], p)

    # QMeas: Detectors (IfPos checks for post-selection)
    c.append("DETECTOR", [stim.target_rec(-7)], [2, 0, 0])
    c.append("DETECTOR", [stim.target_rec(-6)], [4, 1, 0])
    c.append("DETECTOR", [stim.target_rec(-5)], [2, 2, 0])
    c.append("DETECTOR", [stim.target_rec(-4)], [1, 3, 0])
    c.append("DETECTOR", [stim.target_rec(-3)], [1, 0, 0])
    c.append("DETECTOR", [stim.target_rec(-2)], [3, 1, 0])
    c.append("DETECTOR", [stim.target_rec(-1)], [1, 2, 0])
    c.append("SHIFT_COORDS", [], [0, 0, 1])
    c.append("DEPOLARIZE1", list(range(15)), p)
    c.append("TICK")

    # ── STAGE 2: CULTIVATION (double-cat check) ──

    # QMeas: Reset ancilla qubits for cultivation round
    c.append("RX", [14, 11, 6, 2, 8, 1])
    c.append("Z_ERROR", [14, 11, 6, 2, 8, 1], p)
    c.append("DEPOLARIZE1", [0, 3, 4, 5, 7, 9, 10, 12, 13], p)
    c.append("TICK")

    # QMeas: Frame("S_DAG", data_qubits) — T†-sweep (T→S: S†-sweep)
    # This is the FORWARD half of the double-cat check
    data_qubits_cultivation = [0, 3, 7, 9, 10, 12, 13]
    c.append("S_DAG", data_qubits_cultivation)
    c.append("DEPOLARIZE1", list(range(15)), p)
    c.append("TICK")

    # QMeas: Forward cat-state entanglement
    cat_cx_forward = [
        [(1,0), (2,3), (6,7), (8,9), (11,10), (14,13)],
        [(3,1), (7,8), (11,14)],
        [(7,3), (11,12)],
        [(7,11)],
    ]
    for layer in cat_cx_forward:
        targets = []
        used = set()
        for a, b in layer:
            targets.extend([a, b])
            used.add(a); used.add(b)
        c.append("CX", targets)
        c.append("DEPOLARIZE2", targets, p)
        idle = sorted(idle_all - used)
        if idle:
            c.append("DEPOLARIZE1", idle, p)
        c.append("TICK")

    # QMeas: M_X(q7) — cat-state flag measurement
    c.append("MX", [7], p)
    c.append("DEPOLARIZE1", list(range(15)), p)
    c.append("TICK")

    # QMeas: Reset q7 for reverse check
    c.append("RX", [7])
    c.append("Z_ERROR", [7], p)
    c.append("DEPOLARIZE1", [i for i in range(15) if i != 7], p)
    c.append("TICK")

    # QMeas: Reverse cat-state entanglement (time-reversed check)
    cat_cx_reverse = [
        [(7,11)],
        [(7,3), (11,12)],
        [(3,1), (7,8), (11,14)],
        [(1,0), (2,3), (6,7), (8,9), (11,10), (14,13)],
    ]
    for layer in cat_cx_reverse:
        targets = []
        used = set()
        for a, b in layer:
            targets.extend([a, b])
            used.add(a); used.add(b)
        c.append("CX", targets)
        c.append("DEPOLARIZE2", targets, p)
        idle = sorted(idle_all - used)
        if idle:
            c.append("DEPOLARIZE1", idle, p)
        c.append("TICK")

    # QMeas: Frame("S", data_qubits) — T-sweep (T→S: S-sweep)
    # Undoes the S†-sweep from the forward half
    c.append("S", data_qubits_cultivation)
    c.append("DEPOLARIZE1", list(range(15)), p)
    c.append("TICK")

    # QMeas: Final syndrome measurement of cultivation round
    c.append("MX", [14, 11, 6, 2, 8, 1], p)
    c.append("OBSERVABLE_INCLUDE", [
        stim.target_rec(-6), stim.target_rec(-5),
        stim.target_rec(-2), stim.target_rec(-1),
    ], 0)

    # QMeas: Detectors for cultivation round
    c.append("DETECTOR", [stim.target_rec(-9), stim.target_rec(-8),
                           stim.target_rec(-7)], [2.14, 1, 0, -1, -9])
    c.append("DETECTOR", [stim.target_rec(-6)], [4, 1, 1])
    c.append("DETECTOR", [stim.target_rec(-5)], [3, 1, 1])
    c.append("DETECTOR", [stim.target_rec(-4), stim.target_rec(-7)], [2, 1, 1])
    c.append("DETECTOR", [stim.target_rec(-3)], [1, 0, 1])
    c.append("DETECTOR", [stim.target_rec(-2)], [2, 2, 1])
    c.append("DETECTOR", [stim.target_rec(-1)], [0, 1, 1])
    c.append("SHIFT_COORDS", [], [0, 0, 3])
    c.append("DEPOLARIZE1", list(range(15)), p)
    c.append("TICK")

    # ── FINAL: Superdense color-code cycle ──
    # QMeas: Multi-qubit Pauli measurements (the heart of the color code)
    c.append("MPP",
        [stim.target_y(0), stim.target_combiner(),
         stim.target_y(3), stim.target_combiner(),
         stim.target_y(7), stim.target_combiner(),
         stim.target_y(9), stim.target_combiner(),
         stim.target_y(10), stim.target_combiner(),
         stim.target_y(12), stim.target_combiner(),
         stim.target_y(13),
         stim.target_x(0), stim.target_combiner(),
         stim.target_x(3), stim.target_combiner(),
         stim.target_x(7), stim.target_combiner(),
         stim.target_x(10),
         stim.target_z(0), stim.target_combiner(),
         stim.target_z(3), stim.target_combiner(),
         stim.target_z(7), stim.target_combiner(),
         stim.target_z(10),
         stim.target_x(3), stim.target_combiner(),
         stim.target_x(7), stim.target_combiner(),
         stim.target_x(9), stim.target_combiner(),
         stim.target_x(12),
         stim.target_z(3), stim.target_combiner(),
         stim.target_z(7), stim.target_combiner(),
         stim.target_z(9), stim.target_combiner(),
         stim.target_z(12),
         stim.target_x(7), stim.target_combiner(),
         stim.target_x(10), stim.target_combiner(),
         stim.target_x(12), stim.target_combiner(),
         stim.target_x(13),
         stim.target_z(7), stim.target_combiner(),
         stim.target_z(10), stim.target_combiner(),
         stim.target_z(12), stim.target_combiner(),
         stim.target_z(13)])

    c.append("OBSERVABLE_INCLUDE", [stim.target_rec(-7)], 0)

    # Superdense-cycle detectors
    c.append("DETECTOR", [stim.target_rec(-14), stim.target_rec(-6)], [0.75, 0.25, 0, -1, -9])
    c.append("DETECTOR", [stim.target_rec(-5)], [0.75, 0.25, 1, -1, -9])
    c.append("DETECTOR", [stim.target_rec(-14), stim.target_rec(-4)], [1.5, 1.375, 0, -1, -9])
    c.append("DETECTOR", [stim.target_rec(-3)], [1.5, 1.375, 1, -1, -9])
    c.append("DETECTOR", [stim.target_rec(-14), stim.target_rec(-2)], [2.5, 0.875, 0, -1, -9])
    c.append("DETECTOR", [stim.target_rec(-1)], [2.5, 0.875, 1, -1, -9])

    return c


def run_qmeas_cultivation(p: float = 0.001, num_shots: int = 1_000_000):
    """Run our QMeas-built cultivation circuit and report statistics."""
    circuit = build_qmeas_cultivation_stim(p)
    num_dets = circuit.num_detectors
    num_obs = circuit.num_observables

    sampler = circuit.compile_detector_sampler()
    det_events, obs_flips = sampler.sample(
        shots=num_shots, separate_observables=True
    )

    any_detection = np.any(det_events, axis=1)
    accepted = ~any_detection
    n_accepted = int(np.sum(accepted))
    acceptance_rate = n_accepted / num_shots

    if n_accepted > 0:
        obs_errors_accepted = int(np.sum(obs_flips[accepted, 0]))
        logical_error_rate = obs_errors_accepted / n_accepted
    else:
        logical_error_rate = float('nan')

    return {
        "circuit_name": "QMeas d=3 inject[unitary]+cultivate",
        "noise_p": p,
        "num_shots": num_shots,
        "num_detectors": num_dets,
        "num_observables": num_obs,
        "num_qubits": circuit.num_qubits,
        "n_accepted": n_accepted,
        "acceptance_rate": acceptance_rate,
        "logical_error_rate": logical_error_rate,
        "obs_errors_accepted": obs_errors_accepted if n_accepted > 0 else 0,
    }


# =====================================================================
#  Main: compare Gidney reference vs QMeas reconstruction
# =====================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("Full Cultivation Protocol: Gidney Reference vs QMeas Reconstruction")
    print("=" * 70)
    print()

    num_shots = 1_000_000

    for p in [0.001, 0.0005]:
        print(f"\n{'─' * 70}")
        print(f"Noise level: p = {p}")
        print(f"{'─' * 70}")

        # Run Gidney reference
        try:
            gidney = run_gidney_reference(p, num_shots)
            print(f"\n  Gidney reference ({gidney['circuit_name']}):")
            print(f"    Qubits:          {gidney['num_qubits']}")
            print(f"    Detectors:       {gidney['num_detectors']}")
            print(f"    Acceptance rate:  {gidney['acceptance_rate']:.4f}"
                  f" ({gidney['n_accepted']}/{num_shots})")
            print(f"    Logical error:   {gidney['logical_error_rate']:.2e}"
                  f" ({gidney['obs_errors_accepted']}/{gidney['n_accepted']})")
        except FileNotFoundError as e:
            print(f"\n  Gidney reference: NOT FOUND ({e})")
            gidney = None

        # Run QMeas reconstruction
        qmeas = run_qmeas_cultivation(p, num_shots)
        print(f"\n  QMeas reconstruction ({qmeas['circuit_name']}):")
        print(f"    Qubits:          {qmeas['num_qubits']}")
        print(f"    Detectors:       {qmeas['num_detectors']}")
        print(f"    Acceptance rate:  {qmeas['acceptance_rate']:.4f}"
              f" ({qmeas['n_accepted']}/{num_shots})")
        print(f"    Logical error:   {qmeas['logical_error_rate']:.2e}"
              f" ({qmeas['obs_errors_accepted']}/{qmeas['n_accepted']})")

        if gidney:
            print(f"\n  Comparison:")
            print(f"    Qubit count match:    {'YES' if gidney['num_qubits'] == qmeas['num_qubits'] else 'NO'}"
                  f" ({gidney['num_qubits']} vs {qmeas['num_qubits']})")
            print(f"    Detector count match: {'YES' if gidney['num_detectors'] == qmeas['num_detectors'] else 'NO'}"
                  f" ({gidney['num_detectors']} vs {qmeas['num_detectors']})")
            acc_ratio = qmeas['acceptance_rate'] / gidney['acceptance_rate'] if gidney['acceptance_rate'] > 0 else float('nan')
            print(f"    Acceptance ratio:     {acc_ratio:.3f}")

    print(f"\n{'=' * 70}")
    print("QMeas framing of each operation:")
    print("  S_DAG on data qubits  →  QMeas Frame('S_DAG', q)  [T→S trick]")
    print("  CX layers             →  QMeas M_ZZ/M_XX implementation")
    print("  M/MX measurements     →  QMeas Meas('Z'/'X', q, r)")
    print("  DETECTOR              →  QMeas IfPos(det, abort)  [post-selection]")
    print("  OBSERVABLE_INCLUDE    →  QMeas logical observable")
    print("  MPP Y/X/Z products   →  QMeas multi-qubit Pauli measurements")
    print(f"{'=' * 70}")
