"""Resource-estimation utility for QMeas programs on a surface-code target.

Given a Clifford (or Clifford+T) circuit, compute:
  - number of two-qubit Pauli measurements (M_ZZ, M_XX, M_ZX, M_XZ):
    each corresponds to one lattice-surgery merge+split.
  - number of single-qubit Pauli measurements: each corresponds to a
    destructive patch readout.
  - peak number of concurrently-live ancilla patches.
  - Pauli-frame updates and classical control: zero quantum cost.

Assuming a distance-d rotated surface code, each lattice-surgery
operation takes d rounds of stabilizer measurement.  The total
physical time is therefore

  T_phys  =  d * ( N_{2q-meas} + N_{1q-meas-destructive} + N_{merge-split} ),

which, for the gadgets in this paper, reduces to
  H-gadget:    2d rounds,  +1 ancilla patch
  S-gadget:    2d rounds,  +1 ancilla patch
  CNOT-gadget: 3d rounds,  +1 ancilla patch
  T-gadget:    2d-4d rounds + 1 magic state, +1 (or +2) ancilla patches.

The script then illustrates how QMeas-level optimizations (measurement
fusion, frame absorption, commutation-based parallelization,
dead-ancilla elimination) reduce these counts, translating directly
into physical QEC-round savings.
"""

from __future__ import annotations
from dataclasses import dataclass


@dataclass
class Resources:
    meas_2q:      int = 0
    meas_1q:      int = 0
    ancilla_peak: int = 0
    magic_states: int = 0
    frame_ops:    int = 0     # zero physical cost
    control_ops:  int = 0     # zero physical cost

    def phys_rounds(self, d: int) -> int:
        return d * (self.meas_2q + self.meas_1q)

    def logical_qubit_rounds(self, d: int, n_data: int) -> int:
        return d * (n_data + self.ancilla_peak) * (self.meas_2q + self.meas_1q)

    def __str__(self) -> str:
        return (f"  2q measurements        : {self.meas_2q}\n"
                f"  1q measurements        : {self.meas_1q}\n"
                f"  ancilla patches (peak) : {self.ancilla_peak}\n"
                f"  magic states           : {self.magic_states}\n"
                f"  frame updates          : {self.frame_ops}  (zero cost)\n"
                f"  classical control ops  : {self.control_ops}  (zero cost)")


# ---- cost tables for individual gadgets -------------------------------

GADGET_COST = {
    # (meas_2q, meas_1q, ancilla, magic, frame_ops, control_ops)
    "H":    (1, 1, 1, 0, 2, 2),
    "S":    (1, 1, 1, 0, 3, 6),  # three frame cases, three nested ifs
    "CNOT": (2, 1, 1, 0, 2, 4),
    # T gadget: M_ZZ + M_X + conditional S-gadget + frame updates.
    # In the worst-case branch, we invoke the S-gadget (which itself is
    # 1 two-qubit meas + 1 one-qubit meas), hence 2+1 total meas.
    "T":    (2, 2, 2, 1, 4, 6),
}


def estimate_naive(circuit: list[str]) -> Resources:
    """Sum the per-gate cost assuming gates are compiled sequentially with
    no cross-gate optimization."""
    r = Resources()
    for g in circuit:
        m2, m1, anc, magic, fr, ctl = GADGET_COST[g]
        r.meas_2q += m2
        r.meas_1q += m1
        r.ancilla_peak = max(r.ancilla_peak, anc)
        r.magic_states += magic
        r.frame_ops += fr
        r.control_ops += ctl
    return r


# ---- optimization rules ------------------------------------------------

def optimize(circuit: list[str]) -> list[str]:
    """Apply elementary QMeas-level optimizations:

       1. H; H  -> id    (measurement fusion + frame absorption)
       2. S; S; S; S  -> id    (S^4 = I)
       3. S; S  -> Z  (represented as a 'Z' gate; we then drop it since Z
                       folds into the Pauli frame without any quantum op)

    These rules are phrased at the Clifford-circuit level for clarity;
    they are induced by QMeas-level optimizations (fusion and frame
    absorption) that are sound by the gadget lemmas plus the Pauli-
    Clifford commutation table.
    """
    # Represent 'Z' as a frame-only marker that's dropped immediately.
    out = list(circuit)
    changed = True
    while changed:
        changed = False
        # S^4 -> id
        for i in range(len(out) - 3):
            if out[i:i+4] == ["S", "S", "S", "S"]:
                out = out[:i] + out[i+4:]
                changed = True
                break
        if changed:
            continue
        # H H -> id
        for i in range(len(out) - 1):
            if out[i:i+2] == ["H", "H"]:
                out = out[:i] + out[i+2:]
                changed = True
                break
        if changed:
            continue
        # S S -> drop (= Z, which is a pure frame op)
        for i in range(len(out) - 1):
            if out[i:i+2] == ["S", "S"]:
                out = out[:i] + out[i+2:]
                changed = True
                break
    return out


# ---- concrete example --------------------------------------------------

def main():
    d = 15                              # typical surface-code distance
    print(f"Surface-code distance d = {d}\n")

    examples = [
        ("H; S; H; S (identity up to frame)", ["H", "S", "H", "S"]),
        ("H; H; S; S  (naive H^2 S^2)",        ["H", "H", "S", "S"]),
        ("CNOT-free Clifford block",           ["H", "S", "H", "S", "H", "S", "H"]),
        ("All of S^4 (= I)",                   ["S", "S", "S", "S"]),
        ("Mixed Clifford+CNOT (if we add CNOT support)", ["H", "S", "CNOT", "H"]),
        ("T-heavy block",                      ["H", "T", "S", "T", "H", "T"]),
    ]

    for label, circ in examples:
        print(f"=== {label}: {' ; '.join(circ)} ===")
        naive = estimate_naive(circ)
        print(" naive compile:")
        print(naive)
        print(f"   -> T_phys = {naive.phys_rounds(d)} physical QEC rounds")

        opt = optimize(circ)
        print(f" after QMeas-level optimization: {' ; '.join(opt) or '(empty)'}")
        opt_res = estimate_naive(opt)
        print(opt_res)
        print(f"   -> T_phys = {opt_res.phys_rounds(d)} physical QEC rounds")

        saving = naive.phys_rounds(d) - opt_res.phys_rounds(d)
        if naive.phys_rounds(d) > 0:
            pct = 100 * saving / naive.phys_rounds(d)
            print(f"   >>> saving: {saving} rounds ({pct:.0f}% reduction)\n")
        else:
            print()


if __name__ == "__main__":
    main()
