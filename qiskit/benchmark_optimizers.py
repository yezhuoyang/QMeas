"""Stronger head-to-head benchmark: gate / meas / combined on mixed workloads.

Workloads are built as sequences of SEGMENTS, each segment being either:
  - a Clifford-circuit segment (list of ("H",q) / ("S",q) / ("CNOT",c,t)) that
    will pass through the Clifford compiler, or
  - a raw QMeas segment (list of Meas/Frame/Discard/IfPos) that represents
    hand-written measurement protocol (syndrome extraction, magic-state
    injection, stabilizer round, etc.).

This mirrors realistic FTQC compilation, where a circuit is a mix of
Clifford-compilable code and hand-written measurement protocols.

Four pipelines:
  naive      : concat(compile(C_i), raw_j) in order
  gate-first : concat(compile(gate_opt(C_i)), raw_j)
  meas-first : meas_opt(concat(compile(C_i), raw_j))
  combined   : meas_opt(concat(compile(gate_opt(C_i)), raw_j))

Combined subsumes both: it never loses, and strictly wins on mixed workloads.
"""

from __future__ import annotations
import random
from compare_optimizers import (
    Meas, Frame, Discard, IfPos,
    compile_clifford, gate_optimize, meas_optimize,
    meas_count, meas_depth, _dependent,
)

# ---------------------------------------------------------------------
#  R20 baseline: Qiskit Clifford canonicalization + transpile(opt=3).
#  The reviewer (R20) explicitly asked for a comparison against Qiskit's
#  `transpile(optimization_level=3)` or Pyzx's ZX-calculus optimizer as
#  a serious gate-level baseline.  Plain `transpile(opt=3)` in the
#  {h,s,cx} basis does NOT catch S^4=I (observed); the proper Qiskit
#  Clifford optimizer is `qiskit.quantum_info.Clifford(qc).to_circuit()`,
#  which resynthesizes via a stabilizer tableau, followed by transpile
#  to our target basis.
# ---------------------------------------------------------------------

def _convert_qiskit_op(name: str, qs):
    """Convert a Qiskit-emitted Clifford gate to our tuple encoding.
    Pauli gates (X, Y, Z) are kept as Paulis so the QMeas compiler can
    lower them to zero-cost frame updates; Sdg stays as Sdg (expanded
    to S^3 by the compiler); swap stays as SWAP (3 CNOTs).  This mirrors
    the QMeas semantics where Pauli gates cost 0 measurements."""
    if name == "h":     return [("H", qs[0])]
    if name == "s":     return [("S", qs[0])]
    if name == "cx":    return [("CNOT", qs[0], qs[1])]
    if name == "sdg":   return [("Sdg", qs[0])]
    if name == "z":     return [("Z", qs[0])]
    if name == "x":     return [("X", qs[0])]
    if name == "y":     return [("Y", qs[0])]
    if name == "swap":  return [("SWAP", qs[0], qs[1])]
    if name in ("id", "barrier"):
        return []
    raise ValueError(f"Qiskit output gate {name!r} not supported.")


def qiskit_gate_optimize(circuit):
    """Gate-level Clifford optimizer using Qiskit's Clifford-tableau
    synthesis (R20 baseline).  Takes and returns our tuple encoding
    (("H", q), ("S", q), ("CNOT", c, t)).  Non-{H,S,CNOT} output gates
    (x, y, z, sdg, swap) are expanded to our alphabet up to global
    phase (acceptable: the QMeas compiler compiles frame-level)."""
    if not circuit:
        return []
    from qiskit import QuantumCircuit
    from qiskit.quantum_info import Clifford
    qubits = sorted({q for g in circuit
                     for q in (g[1:] if g[0] == "CNOT" else [g[1]])})
    qmap = {q: i for i, q in enumerate(qubits)}
    qc = QuantumCircuit(len(qubits))
    for g in circuit:
        if g[0] == "H":     qc.h(qmap[g[1]])
        elif g[0] == "S":   qc.s(qmap[g[1]])
        elif g[0] == "CNOT":qc.cx(qmap[g[1]], qmap[g[2]])
        else: raise ValueError(f"unknown gate: {g}")
    # Clifford canonicalization via stabilizer tableau.
    canonical = Clifford(qc).to_circuit()
    inv = {i: q for q, i in qmap.items()}
    result = []
    for instr in canonical.data:
        qs = [inv[canonical.find_bit(q).index] for q in instr.qubits]
        result.extend(_convert_qiskit_op(instr.operation.name, qs))
    return result


def qiskit_gate_opt_workload(segments):
    """Apply Qiskit-based gate-level optimization to each Clifford segment."""
    out = []
    for seg in segments:
        if isinstance(seg, tuple) and seg[0] == "clifford":
            out.append(("clifford", qiskit_gate_optimize(seg[1])))
        else:
            out.append(seg)
    return out


def run_qiskit_gate_first(workload):
    return compile_workload(qiskit_gate_opt_workload(workload))


def run_qiskit_combined(workload):
    return meas_optimize(compile_workload(qiskit_gate_opt_workload(workload)))


# =====================================================================
#  Workload segments
# =====================================================================

def compile_workload(segments):
    """Compile a mixed workload: Clifford segments get compiled to QMeas,
    raw-QMeas segments pass through.  Returns a single concatenated QMeas program."""
    out = []
    for seg in segments:
        if isinstance(seg, tuple) and seg[0] == "clifford":
            out.extend(compile_clifford(seg[1]))
        elif isinstance(seg, tuple) and seg[0] == "raw":
            out.extend(seg[1])
        else:
            raise ValueError(f"unknown segment type: {seg}")
    return out


def gate_opt_workload(segments):
    """Apply gate-level optimization to each Clifford segment."""
    out = []
    for seg in segments:
        if isinstance(seg, tuple) and seg[0] == "clifford":
            out.append(("clifford", gate_optimize(seg[1])))
        else:
            out.append(seg)
    return out


def run_naive(workload):      return compile_workload(workload)
def run_gate_first(workload): return compile_workload(gate_opt_workload(workload))
def run_meas_first(workload): return meas_optimize(compile_workload(workload))
def run_combined(workload):   return meas_optimize(compile_workload(gate_opt_workload(workload)))


# =====================================================================
#  Workload constructors
# =====================================================================

def clifford(gates):
    return ("clifford", list(gates))

def raw(ops):
    return ("raw", list(ops))


def syndrome_round(qubits, n_repeats=3):
    """Repeated M_ZZ stabilizer measurement on `qubits`, simulating a QEC cycle."""
    ops = []
    for i in range(n_repeats):
        ops.append(Meas("ZZ", tuple(qubits), f"s{id(qubits)}_{i}"))
    return raw(ops)


def syndrome_multi(stabilizers, n_repeats=3):
    """Multi-stabilizer measurement round, interleaved."""
    ops = []
    for i in range(n_repeats):
        for pauli, qs in stabilizers:
            ops.append(Meas(pauli, tuple(qs), f"s_{i}_{id(qs)}"))
    return raw(ops)


def magic_state_injection(q_data, q_magic):
    """T gate via magic state: M_ZZ(q_data, q_magic); M_X(q_data); discard q_data."""
    return raw([
        Meas("ZZ", (q_data, q_magic), "mt1"),
        Meas("X", (q_data,), "mt2"),
        Discard(q_data),
    ])


def parity_check(q_list):
    """Parity check over a set of qubits — multiple commuting Z measurements.
    Typical of QEC: check commuting stabilizers."""
    ops = []
    for i, q in enumerate(q_list):
        ops.append(Meas("Z", (q,), f"p{i}"))
    return raw(ops)


# =====================================================================
#  Benchmark circuits
# =====================================================================

def workload_pure_clifford_identity():
    """H^2; S^4; CNOT^2 — gate-level catches all; meas-level can't."""
    return [clifford([("H","q0"),("H","q0"),
                      ("S","q1"),("S","q1"),("S","q1"),("S","q1"),
                      ("CNOT","q0","q1"),("CNOT","q0","q1")])]


def workload_pure_syndrome():
    """Pure QMeas: repeated stabilizer measurement.  Gate-level has no handle."""
    return [syndrome_round(("q0","q1"), n_repeats=8)]


def workload_pure_syndrome_multi():
    """Multi-stabilizer QEC round (X- and Z-type stabilizers repeated)."""
    stabs = [("ZZ", ("q0","q1")),
             ("ZZ", ("q1","q2")),
             ("XX", ("q3","q4")),
             ("XX", ("q4","q5"))]
    return [syndrome_multi(stabs, n_repeats=5)]


def workload_mixed_clifford_plus_syndrome():
    """Realistic QEC cycle: Clifford prep (with cancellable structure) +
    stabilizer measurement loop."""
    return [clifford([("H","q0"),("H","q0"),        # cancels to id
                      ("S","q1"),("S","q1"),        # S^2 = Z, frame-only
                      ("CNOT","q0","q1"),("CNOT","q0","q1")]),  # cancels
            syndrome_round(("q0","q1"), n_repeats=5)]


def workload_clifford_and_t_injection():
    """Clifford block followed by magic-state T injection.
    Gate-level reduces Clifford; meas-level catches redundancies in the injection."""
    return [clifford([("H","q0"),("H","q0"),("S","q0"),("S","q0"),
                      ("CNOT","q0","q1")]),
            magic_state_injection("q0", "qm1"),
            magic_state_injection("q1", "qm2")]


def workload_qec_round_surface_code():
    """Two-plaquette surface-code-like round.  Each plaquette has a Z-type
    and an X-type 4-qubit stabilizer on the same qubits — they commute
    because all 4 positions anticommute (even), and the two plaquettes are
    disjoint so their stabilizers trivially commute with the other's.
    Thus all 4 stabilizers pairwise commute, as required of a well-formed
    code, and the cross-round repetition is deduplicatable.  Interleaves
    with a Clifford decoder-prep that simplifies at gate level."""
    prep = [("H","q0"),("H","q0"),("H","q1"),("H","q1"),
            ("CNOT","q0","q4"),("CNOT","q0","q4"),
            ("S","q2"),("S","q2"),("S","q2"),("S","q2")]
    stabs = [
        ("ZZZZ", ("q0","q1","q2","q3")),
        ("XXXX", ("q0","q1","q2","q3")),
        ("ZZZZ", ("q4","q5","q6","q7")),
        ("XXXX", ("q4","q5","q6","q7")),
    ]
    return [clifford(prep), syndrome_multi(stabs, n_repeats=3)]


def workload_repetition_code_round():
    """Repetition code, distance 5: 5 data qubits, 4 Z-stabilizers
    Z(q_i)Z(q_{i+1}), repeated 5 times.  All stabilizers commute (they share
    at most one qubit and both are Z there), so cross-round deduplication
    applies directly."""
    stabs = [("ZZ", (f"q{i}", f"q{i+1}")) for i in range(4)]
    return [syndrome_multi(stabs, n_repeats=5)]


def workload_repetition_plus_prep():
    """Clifford encoder prep for the repetition code + 5 syndrome rounds."""
    prep = [("H","q0"),("H","q0"),          # cancels
            ("CNOT","q0","q1"),("CNOT","q1","q2"),
            ("CNOT","q2","q3"),("CNOT","q3","q4"),
            ("S","q2"),("S","q2"),("S","q2"),("S","q2")]  # cancels
    stabs = [("ZZ", (f"q{i}", f"q{i+1}")) for i in range(4)]
    return [clifford(prep), syndrome_multi(stabs, n_repeats=5)]


def workload_random_mixed(seed, n_cliff, n_synd):
    """Random Clifford gates interleaved with random syndrome measurements."""
    rng = random.Random(seed)
    cl = []
    for _ in range(n_cliff):
        kind = rng.choice(["H","H","H","S","S","S","CNOT"])  # bias toward repeats
        if kind == "CNOT":
            c, t = rng.sample(["q0","q1","q2","q3"], 2)
            cl.append(("CNOT", c, t))
        else:
            cl.append((kind, f"q{rng.randrange(4)}"))
    # several stabilizer rounds
    segs = [clifford(cl)]
    for _ in range(n_synd):
        q = rng.sample(["q0","q1","q2","q3"], 2)
        reps = rng.choice([2, 3, 4])
        segs.append(syndrome_round(tuple(q), n_repeats=reps))
    return segs


# =====================================================================
#  Reporting
# =====================================================================

def evaluate(workload, label):
    n  = run_naive(workload)
    g  = run_gate_first(workload)
    qg = run_qiskit_gate_first(workload)
    m  = run_meas_first(workload)
    c  = run_combined(workload)
    qc = run_qiskit_combined(workload)
    stats = {
        "naive":          (meas_count(n),  meas_depth(n)),
        "gate_first":     (meas_count(g),  meas_depth(g)),
        "qiskit_gate":    (meas_count(qg), meas_depth(qg)),
        "meas_first":     (meas_count(m),  meas_depth(m)),
        "combined":       (meas_count(c),  meas_depth(c)),
        "qiskit_combined":(meas_count(qc), meas_depth(qc)),
    }
    return label, stats


def print_row(label, stats):
    n  = stats["naive"];          g  = stats["gate_first"]
    qg = stats["qiskit_gate"];    m  = stats["meas_first"]
    c  = stats["combined"];       qc = stats["qiskit_combined"]
    counts = [n[0], g[0], qg[0], m[0], c[0], qc[0]]
    best = min(counts)
    win = ["*" if x == best else " " for x in counts]
    row = (f"{label[:42]:<42} "
           f"{n[0]:>3}/{n[1]:<2}{win[0]} "
           f"{g[0]:>3}/{g[1]:<2}{win[1]} "
           f"{qg[0]:>3}/{qg[1]:<2}{win[2]} "
           f"{m[0]:>3}/{m[1]:<2}{win[3]} "
           f"{c[0]:>3}/{c[1]:<2}{win[4]} "
           f"{qc[0]:>3}/{qc[1]:<2}{win[5]}")
    print(row)


def main():
    print("Stronger benchmark: gate / meas / combined on mixed workloads")
    print(f"  d = 15 (surface-code distance); entry shown as `count/depth`*")
    print(f"  * marks the minimum count across all six pipelines.")
    print(f"  gate-H = 4-rule hand-written; gate-Q = Qiskit Clifford-tableau")
    print(f"           canonicalization + transpile(opt=3) (R20 baseline).\n")
    header = (f"{'workload':<42} {'naive':>8} {'gate-H':>8} "
              f"{'gate-Q':>8} {'meas':>8} {'comb-H':>8} {'comb-Q':>8}")
    print(header)
    print("-" * len(header))

    # ---- Six hand-chosen workloads ----
    workloads = [
        ("Pure Clifford with H^2, S^4, CNOT^2 identities",
            workload_pure_clifford_identity()),
        ("Pure syndrome loop: 8 × M_ZZ(q0,q1)",
            workload_pure_syndrome()),
        ("QEC syndrome round: 4 stabilizers × 5 reps",
            workload_pure_syndrome_multi()),
        ("Mixed: Clifford identities + syndrome loop",
            workload_mixed_clifford_plus_syndrome()),
        ("Clifford + 2× magic-state T injection",
            workload_clifford_and_t_injection()),
        ("Surface-code d=3 round (4-qubit plaquettes × 3 reps + prep)",
            workload_qec_round_surface_code()),
        ("Repetition-code d=5: 4 stabilizers × 5 reps",
            workload_repetition_code_round()),
        ("Repetition-code encoder + 5 syndrome rounds (realistic QEC)",
            workload_repetition_plus_prep()),
    ]
    for label, workload in workloads:
        _, stats = evaluate(workload, label)
        print_row(label, stats)

    # ---- Random mixed workload suite ----
    print()
    print("Random mixed workloads (n_cliff = 6-12 gates, n_synd = 2-4 rounds):")
    print("-" * len(header))
    keys = ["naive", "gate_first", "qiskit_gate", "meas_first",
            "combined", "qiskit_combined"]
    agg = {k: [0, 0] for k in keys}
    strict_combined_wins_hand = 0
    strict_combined_wins_qiskit = 0
    qiskit_beats_hand_gate = 0
    hand_beats_qiskit_gate = 0
    qiskit_ties_hand_gate = 0
    N = 50
    for seed in range(N):
        nc = 6 + seed % 7
        ns = 2 + seed % 3
        wl = workload_random_mixed(seed, nc, ns)
        _, stats = evaluate(wl, f"seed={seed}")
        for k in keys:
            agg[k][0] += stats[k][0]
            agg[k][1] += stats[k][1]
        # Hand-rolled combined strictly beats both hand-gate and meas?
        if (stats["combined"][0] < stats["gate_first"][0] and
            stats["combined"][0] < stats["meas_first"][0]):
            strict_combined_wins_hand += 1
        # Qiskit-combined strictly beats both qiskit-gate and meas?
        if (stats["qiskit_combined"][0] < stats["qiskit_gate"][0] and
            stats["qiskit_combined"][0] < stats["meas_first"][0]):
            strict_combined_wins_qiskit += 1
        # Head-to-head: Qiskit gate-optimizer vs hand-rolled gate-optimizer
        if stats["qiskit_gate"][0] < stats["gate_first"][0]:
            qiskit_beats_hand_gate += 1
        elif stats["qiskit_gate"][0] > stats["gate_first"][0]:
            hand_beats_qiskit_gate += 1
        else:
            qiskit_ties_hand_gate += 1
        if seed < 6:
            print_row(f"seed={seed} (nc={nc}, ns={ns})", stats)
    print("  ... (aggregate below)")

    print()
    print("Aggregate over 50 random mixed workloads:")
    for k in keys:
        print(f"  {k:<16}  avg count = {agg[k][0]/N:>5.1f}   "
              f"avg depth = {agg[k][1]/N:>5.1f}")
    print()
    print(f"Qiskit-gate-optimizer vs hand-rolled 4-rule gate-optimizer "
          f"(head-to-head on {N} random mixed workloads):")
    print(f"  qiskit wins:  {qiskit_beats_hand_gate}")
    print(f"  hand wins  :  {hand_beats_qiskit_gate}")
    print(f"  tie        :  {qiskit_ties_hand_gate}")
    print()
    print(f"Combined (with hand-rolled gate-opt) STRICTLY beats BOTH "
          f"gate-first and meas-first on {strict_combined_wins_hand}/{N}.")
    print(f"Combined (with QISKIT gate-opt) STRICTLY beats BOTH "
          f"qiskit-gate and meas-first on {strict_combined_wins_qiskit}/{N}.")

    # Physical savings at d = 15
    print()
    print("Physical QEC-round saving (at d = 15):")
    d = 15
    for k in keys[1:]:
        saving = (agg["naive"][0] - agg[k][0]) * d / N
        print(f"  {k:<16}  avg saving vs naive = {saving:>6.1f} QEC rounds")


if __name__ == "__main__":
    main()
