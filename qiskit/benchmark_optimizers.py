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
    n = run_naive(workload)
    g = run_gate_first(workload)
    m = run_meas_first(workload)
    c = run_combined(workload)
    stats = {
        "naive":      (meas_count(n), meas_depth(n)),
        "gate_first": (meas_count(g), meas_depth(g)),
        "meas_first": (meas_count(m), meas_depth(m)),
        "combined":   (meas_count(c), meas_depth(c)),
    }
    return label, stats


def print_row(label, stats):
    n  = stats["naive"];      g = stats["gate_first"]
    m  = stats["meas_first"]; c = stats["combined"]
    # Winners on COUNT
    counts = [n[0], g[0], m[0], c[0]]
    best = min(counts)
    win_mask = ["*" if x == best else " " for x in counts]
    row = (f"{label[:48]:<48}  "
           f"{n[0]:>3}/{n[1]:<2}{win_mask[0]}  "
           f"{g[0]:>3}/{g[1]:<2}{win_mask[1]}  "
           f"{m[0]:>3}/{m[1]:<2}{win_mask[2]}  "
           f"{c[0]:>3}/{c[1]:<2}{win_mask[3]}")
    print(row)


def main():
    print("Stronger benchmark: gate / meas / combined on mixed workloads")
    print(f"  d = 15 (surface-code distance); entry shown as `count/depth`*")
    print(f"  * marks the minimum count across pipelines.\n")
    header = f"{'workload':<48}  {'naive':>8}  {'gate-1st':>8}  {'meas-1st':>8}  {'combined':>8}"
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
    agg = {"naive":[0,0], "gate_first":[0,0], "meas_first":[0,0], "combined":[0,0]}
    wins_c = {"gate_first":0, "meas_first":0, "combined":0, "tie":0}
    wins_d = {"gate_first":0, "meas_first":0, "combined":0, "tie":0}
    strict_combined_wins = 0
    N = 50
    for seed in range(N):
        nc = 6 + seed % 7
        ns = 2 + seed % 3
        wl = workload_random_mixed(seed, nc, ns)
        _, stats = evaluate(wl, f"seed={seed}")
        for k in agg:
            agg[k][0] += stats[k][0]
            agg[k][1] += stats[k][1]
        c_counts = [stats["gate_first"][0], stats["meas_first"][0], stats["combined"][0]]
        best_c = min(c_counts)
        if stats["combined"][0] == best_c and stats["combined"][0] < stats["gate_first"][0] \
           and stats["combined"][0] < stats["meas_first"][0]:
            strict_combined_wins += 1
        if stats["gate_first"][0] < stats["meas_first"][0]: wins_c["gate_first"] += 1
        elif stats["meas_first"][0] < stats["gate_first"][0]: wins_c["meas_first"] += 1
        else: wins_c["tie"] += 1
        if stats["gate_first"][1] < stats["meas_first"][1]: wins_d["gate_first"] += 1
        elif stats["meas_first"][1] < stats["gate_first"][1]: wins_d["meas_first"] += 1
        else: wins_d["tie"] += 1
        if seed < 6:
            print_row(f"seed={seed} (nc={nc}, ns={ns})", stats)
    print("  ... (aggregate below)")

    print()
    print("Aggregate over 50 random mixed workloads:")
    for k in ["naive", "gate_first", "meas_first", "combined"]:
        print(f"  {k:<12}  avg count = {agg[k][0]/N:>5.1f}   avg depth = {agg[k][1]/N:>5.1f}")
    print()
    print("Pairwise comparison (gate-first vs meas-first):")
    print(f"  count wins:  gate={wins_c['gate_first']}  meas={wins_c['meas_first']}  tie={wins_c['tie']}")
    print(f"  depth wins:  gate={wins_d['gate_first']}  meas={wins_d['meas_first']}  tie={wins_d['tie']}")
    print()
    print(f"Combined STRICTLY beats BOTH gate-first and meas-first on "
          f"{strict_combined_wins}/{N} random mixed workloads.")

    # Physical savings at d = 15
    print()
    print("Physical QEC-round saving (at d = 15):")
    d = 15
    for k in ["gate_first", "meas_first", "combined"]:
        saving = (agg["naive"][0] - agg[k][0]) * d / N
        print(f"  {k:<12}  avg saving vs naive = {saving:>6.1f} QEC rounds")


if __name__ == "__main__":
    main()
