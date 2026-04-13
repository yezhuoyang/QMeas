"""Re-validate the three chosen gadgets on many random seeds and print a
correction-table summary that we can mirror in the Lean proofs."""

from __future__ import annotations
import numpy as np
from validate_gadgets import (
    I, X, Y, Z, H_gate, S_gate, PAULI, pauli_string_op,
    measure, reduce_to_qubit, state_after_correction, density_close,
    random_pure_state,
)

CNOT_mat = np.array(
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex
)


def verify_gate_gadget(name, target_op, ancilla_state, m1_str, m2_str,
                       n_seeds: int = 50):
    """Verify a 2-meas single-qubit gate gadget. Print branch -> required
    correction Pauli (intersection over all random seeds)."""
    print(f"\n=== {name} :: ancilla={ancilla_state}, M_{m1_str}(q,a); M_{m2_str}(q) ===")
    if ancilla_state == "0":
        a = np.array([1, 0], dtype=complex)
    elif ancilla_state == "+":
        a = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    else:
        raise ValueError(ancilla_state)
    M1 = pauli_string_op(m1_str)
    M2 = pauli_string_op(m2_str + "I")

    branch_correction: dict = {}
    for seed in range(n_seeds):
        psi = random_pure_state(seed=seed)
        target_state = target_op @ psi
        target_rho = np.outer(target_state, target_state.conj())
        state0 = np.kron(psi, a)
        for r1 in (+1, -1):
            p1, s1 = measure(state0, M1, r1)
            if p1 == 0:
                continue
            for r2 in (+1, -1):
                p2, s2 = measure(s1, M2, r2)
                if p2 == 0:
                    continue
                rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
                valid = []
                for c in ("I", "X", "Y", "Z"):
                    if density_close(state_after_correction(rho_a, PAULI[c]), target_rho):
                        valid.append(c)
                prev = branch_correction.get((r1, r2))
                if prev is None:
                    branch_correction[(r1, r2)] = set(valid)
                else:
                    branch_correction[(r1, r2)] = prev & set(valid)
    all_ok = all(len(v) == 1 for v in branch_correction.values())
    for k in sorted(branch_correction):
        v = branch_correction[k]
        sym = "OK" if len(v) == 1 else "AMBIG"
        print(f"  branch r1={k[0]:+d}, r2={k[1]:+d}  correction = {sorted(v)}  [{sym}]")
    print(f"  >>> {'PASS' if all_ok else 'FAIL'} on {n_seeds} seeds")
    return branch_correction


def verify_cnot_gadget(n_seeds: int = 50):
    print(f"\n=== CNOT :: ancilla=|+>, M_ZZ(c,a); M_XX(a,t); M_Z(a) ===")
    plus = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    # qubit ordering: c=0, t=1, a=2
    M1 = pauli_string_op("ZIZ")  # ZZ on (c,a)
    M2 = pauli_string_op("IXX")  # XX on (t,a)? careful.
    # ZZ(c,a) at positions c=0, a=2: Z I Z  ✓
    # XX(a,t) at positions t=1, a=2: I X X  ✓
    M3 = pauli_string_op("IIZ")  # Z on a

    rng = np.random.default_rng(2026)
    branch_correction: dict = {}
    for seed in range(n_seeds):
        v = rng.normal(size=4) + 1j * rng.normal(size=4)
        v = v / np.linalg.norm(v)
        target_ct = CNOT_mat @ v
        target_rho_ct = np.outer(target_ct, target_ct.conj())
        state0 = np.kron(v, plus)  # (c,t,a)
        for r1 in (+1, -1):
            p1, s1 = measure(state0, M1, r1)
            if p1 == 0:
                continue
            for r2 in (+1, -1):
                p2, s2 = measure(s1, M2, r2)
                if p2 == 0:
                    continue
                for r3 in (+1, -1):
                    p3, s3 = measure(s2, M3, r3)
                    if p3 == 0:
                        continue
                    # trace out a (qubit 2)
                    rho_full = np.outer(s3, s3.conj()).reshape([2] * 6)
                    rho_ct = np.einsum("ijkmnk->ijmn", rho_full).reshape(4, 4)
                    valid = []
                    for cc in ("I", "X", "Y", "Z"):
                        for ct in ("I", "X", "Y", "Z"):
                            corr = np.kron(PAULI[cc], PAULI[ct])
                            if density_close(state_after_correction(rho_ct, corr), target_rho_ct):
                                valid.append((cc, ct))
                    prev = branch_correction.get((r1, r2, r3))
                    if prev is None:
                        branch_correction[(r1, r2, r3)] = set(valid)
                    else:
                        branch_correction[(r1, r2, r3)] = prev & set(valid)
    all_ok = all(len(v) >= 1 for v in branch_correction.values())
    for k in sorted(branch_correction):
        v = branch_correction[k]
        # prefer pure XZ-only corrections (no Y) for clean Pauli frame
        nice = sorted(v, key=lambda p: (("Y" in p), p))
        print(f"  branch r1={k[0]:+d}, r2={k[1]:+d}, r3={k[2]:+d}  corrections={[''.join(p) for p in nice[:3]]}")
    print(f"  >>> {'PASS' if all_ok else 'FAIL'} on {n_seeds} seeds")
    return branch_correction


if __name__ == "__main__":
    print("Verifying chosen QMeas gadgets on 50 random seeds each.")
    verify_gate_gadget("H", H_gate, "0", "ZX", "X")
    verify_gate_gadget("S", S_gate, "+", "ZZ", "Y")
    verify_cnot_gadget()
