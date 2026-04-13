"""Verify the T-gate magic-state-injection gadget:
  input |ψ⟩ on q, magic state |A⟩ = (|0⟩ + e^{iπ/4}|1⟩)/√2 on m.
  r1 := M_{ZZ}(q, m)
  r2 := M_X(q)
  discard q.
For each branch, find the Clifford correction on m that yields T|ψ⟩."""

from __future__ import annotations
import numpy as np
from validate_gadgets import (
    I, X, Y, Z, PAULI, pauli_string_op, measure,
    reduce_to_qubit, state_after_correction, density_close, random_pure_state,
)

# T gate
T_gate = np.array([[1, 0], [0, np.exp(1j * np.pi / 4)]], dtype=complex)
S_gate = np.array([[1, 0], [0, 1j]], dtype=complex)
H_gate = (1 / np.sqrt(2)) * np.array([[1, 1], [1, -1]], dtype=complex)

# magic state |A⟩ = T|+⟩
A_state = T_gate @ np.array([1, 1], dtype=complex) / np.sqrt(2)
print(f"|A> = {A_state}")

# Clifford corrections to try (all 24 single-qubit Clifford operators,
# but in practice only {I, X, Y, Z, S, SX, SY, SZ, S^dag, ...} are
# relevant).
CANDIDATES = {}
for name, op in [
    ("I", I), ("X", X), ("Y", Y), ("Z", Z),
    ("S", S_gate), ("SX", S_gate @ X), ("SY", S_gate @ Y), ("SZ", S_gate @ Z),
    ("XS", X @ S_gate), ("YS", Y @ S_gate), ("ZS", Z @ S_gate),
    ("Sd", S_gate.conj().T), ("SdX", S_gate.conj().T @ X),
    ("SdZ", S_gate.conj().T @ Z),
]:
    CANDIDATES[name] = op


def verify_T(n_seeds: int = 30):
    print("\n=== T-gate magic-state-injection gadget ===")
    ZZ = pauli_string_op("ZZ")
    XI = pauli_string_op("XI")
    branch_correction: dict = {}
    for seed in range(n_seeds):
        psi = random_pure_state(seed=seed)
        target_state = T_gate @ psi
        target_rho = np.outer(target_state, target_state.conj())
        joint = np.kron(psi, A_state)       # (q, m)
        for r1 in (+1, -1):
            p1, s1 = measure(joint, ZZ, r1)
            if p1 == 0:
                continue
            for r2 in (+1, -1):
                p2, s2 = measure(s1, XI, r2)
                if p2 == 0:
                    continue
                rho_m = reduce_to_qubit(s2, n_qubits=2, target=1)
                valid = []
                for name, op in CANDIDATES.items():
                    rho_corr = state_after_correction(rho_m, op)
                    if density_close(rho_corr, target_rho):
                        valid.append(name)
                prev = branch_correction.get((r1, r2))
                if prev is None:
                    branch_correction[(r1, r2)] = set(valid)
                else:
                    branch_correction[(r1, r2)] = prev & set(valid)
    for (r1, r2), corrs in sorted(branch_correction.items()):
        nice = sorted(corrs)
        print(f"  branch ({r1:+d}, {r2:+d})  valid corrections: {nice}")


if __name__ == "__main__":
    verify_T()
