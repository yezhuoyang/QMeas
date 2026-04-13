"""Search for correct measurement-based gadgets that realize H and CNOT."""

from __future__ import annotations
import numpy as np
from validate_gadgets import (
    I, X, Y, Z, H_gate, S_gate, PAULI, pauli_string_op, measure,
    reduce_to_qubit, state_after_correction, density_close, random_pure_state,
)


def search_single_qubit_gate(target_op: np.ndarray, name: str, n_random: int = 5):
    """Search all 2-qubit-then-single-qubit measurement patterns with ancilla
    in {|0>, |+>, |+i>} that realize target_op|psi> on the ancilla up to a Pauli
    correction. Validate on `n_random` random inputs."""
    ancilla_states = {
        "0": np.array([1, 0], dtype=complex),
        "+": (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex),
        "+i": (1 / np.sqrt(2)) * np.array([1, 1j], dtype=complex),
    }
    paulis = ["I", "X", "Y", "Z"]
    two_qubit = [a + b for a in paulis for b in paulis if (a, b) != ("I", "I")]
    one_qubit = ["X", "Y", "Z"]

    psis = [random_pure_state(seed=s) for s in range(n_random)]

    print(f"\n=== Searching gadgets for {name} ===")
    found = []
    for anc_name, anc_state in ancilla_states.items():
        for m1 in two_qubit:
            for m2 in one_qubit:
                # check: every branch deterministically picks one Pauli correction,
                # consistent across all input states
                consistent = True
                branch_corrections: dict = {}
                for psi in psis:
                    state0 = np.kron(psi, anc_state)
                    M1 = pauli_string_op(m1)
                    M2 = pauli_string_op(m2 + "I")
                    target_state = target_op @ psi
                    target_rho = np.outer(target_state, target_state.conj())
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
                            for c in paulis:
                                if density_close(state_after_correction(rho_a, PAULI[c]), target_rho):
                                    valid.append(c)
                            if not valid:
                                consistent = False
                                break
                            prev = branch_corrections.get((r1, r2))
                            if prev is None:
                                branch_corrections[(r1, r2)] = set(valid)
                            else:
                                branch_corrections[(r1, r2)] = prev & set(valid)
                                if not branch_corrections[(r1, r2)]:
                                    consistent = False
                                    break
                        if not consistent:
                            break
                    if not consistent:
                        break
                if consistent and branch_corrections:
                    found.append((anc_name, m1, m2, branch_corrections))
    if not found:
        print(f"  no 2-meas gadget found for {name}")
        return
    print(f"  found {len(found)} candidate gadget(s):")
    for anc, m1, m2, bc in found[:30]:
        bc_str = ", ".join(f"{k}->{sorted(v)}" for k, v in sorted(bc.items()))
        print(f"    ancilla=|{anc}>  M_{m1}(q,a); M_{m2}(q)  corrections: {bc_str}")


# CNOT gadget search using one ancilla
CNOT_mat = np.array(
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex
)


def search_cnot_one_ancilla(n_random: int = 3):
    """Look for: ancilla a in |+> or |0>, three measurements:
       M_P1(c,a), M_P2(a,t), M_P3(a). Check all combos."""
    print("\n=== Searching one-ancilla CNOT gadgets ===")
    ancilla_states = {
        "0": np.array([1, 0], dtype=complex),
        "+": (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex),
    }
    paulis = ["I", "X", "Y", "Z"]
    two_qubit = [a + b for a in paulis for b in paulis if a != "I" and b != "I"]
    one_qubit = ["X", "Y", "Z"]

    rng = np.random.default_rng(7)
    psis = []
    for _ in range(n_random):
        v = rng.normal(size=4) + 1j * rng.normal(size=4)
        v = v / np.linalg.norm(v)
        psis.append(v)

    found = []
    # qubit ordering: c=0, t=1, a=2
    def op3(s):
        return pauli_string_op(s)

    for anc_name, anc_state in ancilla_states.items():
        for p1 in two_qubit:  # M_{P1} on (c, a)  → string p1[0] I p1[1]  positions (c, t, a)
            for p2 in two_qubit:  # M_{P2} on (a, t) → string I p2[1] p2[0]
                for p3 in one_qubit:  # M_{P3} on a → I I p3
                    M1 = op3(p1[0] + "I" + p1[1])
                    M2 = op3("I" + p2[1] + p2[0])
                    M3 = op3("II" + p3)
                    consistent = True
                    branch_correction: dict = {}
                    for psi in psis:
                        state0 = np.kron(psi, anc_state)
                        target_ct = CNOT_mat @ psi
                        target_rho_ct = np.outer(target_ct, target_ct.conj())
                        for r1 in (+1, -1):
                            pp1, s1 = measure(state0, M1, r1)
                            if pp1 == 0:
                                continue
                            for r2 in (+1, -1):
                                pp2, s2 = measure(s1, M2, r2)
                                if pp2 == 0:
                                    continue
                                for r3 in (+1, -1):
                                    pp3, s3 = measure(s2, M3, r3)
                                    if pp3 == 0:
                                        continue
                                    # reduce to (c, t)
                                    rho_full = np.outer(s3, s3.conj()).reshape([2] * 6)
                                    # axes order: c_row, t_row, a_row, c_col, t_col, a_col
                                    rho = np.einsum("ijkijl->ijkl", np.einsum("abcdef->abcdef", rho_full))
                                    # actually trace out a (axes 2 and 5)
                                    rho = np.einsum("ijkdef->ijdef", rho_full)  # contract row a with col a? need to keep diag
                                    # Easier: explicit partial trace
                                    rho_full_mat = np.outer(s3, s3.conj())
                                    rho_full_t = rho_full_mat.reshape([2, 2, 2, 2, 2, 2])
                                    # partial trace over qubit 2 (a): sum over its diag axis
                                    rho_ct = np.einsum("ijkmnk->ijmn", rho_full_t).reshape(4, 4)
                                    # try all 16 Pauli corrections on (c, t)
                                    valid = []
                                    for cc in paulis:
                                        for ct in paulis:
                                            corr = np.kron(PAULI[cc], PAULI[ct])
                                            if density_close(state_after_correction(rho_ct, corr), target_rho_ct):
                                                valid.append((cc, ct))
                                    if not valid:
                                        consistent = False
                                        break
                                    prev = branch_correction.get((r1, r2, r3))
                                    if prev is None:
                                        branch_correction[(r1, r2, r3)] = set(valid)
                                    else:
                                        branch_correction[(r1, r2, r3)] = prev & set(valid)
                                        if not branch_correction[(r1, r2, r3)]:
                                            consistent = False
                                            break
                                if not consistent:
                                    break
                            if not consistent:
                                break
                        if not consistent:
                            break
                    if consistent and branch_correction:
                        found.append((anc_name, p1, p2, p3, branch_correction))
    print(f"  found {len(found)} one-ancilla gadget(s)")
    for anc, p1, p2, p3, bc in found[:10]:
        print(f"\n  ancilla=|{anc}>  M_{p1}(c,a); M_{p2}(a,t); M_{p3}(a)")
        for k, v in sorted(bc.items()):
            print(f"    branch {k}: corrections (c,t) = {sorted(v)}")


if __name__ == "__main__":
    search_single_qubit_gate(H_gate, "H")
    search_single_qubit_gate(S_gate, "S")
    search_cnot_one_ancilla(n_random=3)
