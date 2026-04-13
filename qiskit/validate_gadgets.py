"""
Validate the QMeas gadgets from the paper by exhaustive simulation.

For each claimed gadget we:
  1. Build the measurement-based program as a Qiskit Statevector simulation,
     iterating over all measurement outcomes.
  2. For each branch, compare the post-measurement state on the output qubit
     (after applying the byproduct Pauli stored in the frame) against the
     state produced by the unitary action of the claimed gate.
  3. Print pass/fail per branch and overall.

If the paper's gadget is wrong, we surface that here BEFORE formalizing in Lean.
"""

from __future__ import annotations

import numpy as np
from qiskit.quantum_info import Statevector, Operator

# --- single-qubit operators ------------------------------------------------

I = np.array([[1, 0], [0, 1]], dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
H_gate = (1 / np.sqrt(2)) * np.array([[1, 1], [1, -1]], dtype=complex)
S_gate = np.array([[1, 0], [0, 1j]], dtype=complex)

PAULI = {"I": I, "X": X, "Y": Y, "Z": Z}


def kron_all(ops):
    out = np.array([[1.0 + 0.0j]])
    for op in ops:
        out = np.kron(out, op)
    return out


def pauli_string_op(s: str) -> np.ndarray:
    """e.g. 'ZZ' -> Z⊗Z, 'XI' -> X⊗I."""
    return kron_all([PAULI[c] for c in s])


def projector_eigen(op: np.ndarray, eigval: int) -> np.ndarray:
    """Projector onto the +1 or -1 eigenspace of a Hermitian Pauli operator
    with eigenvalues ±1."""
    d = op.shape[0]
    return 0.5 * (np.eye(d, dtype=complex) + eigval * op)


def measure(state: np.ndarray, op: np.ndarray, eigval: int) -> tuple[float, np.ndarray]:
    """Project state onto eigval-eigenspace of op. Return (prob, normalized state).
    If prob == 0, returns (0, zeros)."""
    P = projector_eigen(op, eigval)
    new = P @ state
    prob = float(np.real(np.vdot(new, new)))
    if prob < 1e-14:
        return 0.0, np.zeros_like(state)
    return prob, new / np.sqrt(prob)


def reduce_to_qubit(state: np.ndarray, n_qubits: int, target: int) -> np.ndarray:
    """Trace out all qubits except `target`, return density matrix (2x2).
    Qubit ordering: qubit 0 is leftmost (big-endian like our kron usage)."""
    rho_full = np.outer(state, state.conj())
    dim = 2 ** n_qubits
    rho_full = rho_full.reshape([2] * n_qubits + [2] * n_qubits)
    # contract over all axes except target (row + col)
    keep_row = target
    keep_col = target + n_qubits
    # transpose so that kept axes are first
    axes = [keep_row, keep_col] + [i for i in range(2 * n_qubits) if i not in (keep_row, keep_col)]
    rho_full = np.transpose(rho_full, axes)
    rho_full = rho_full.reshape(2, 2, -1, 2 ** (n_qubits - 1))
    # trace over the remaining n-1 qubits (axes 2 and 3 are equal-dim, take diag)
    rho = np.einsum("ijkk->ij", rho_full.reshape(2, 2, 2 ** (n_qubits - 1), 2 ** (n_qubits - 1)))
    return rho


def state_after_correction(rho: np.ndarray, correction: np.ndarray) -> np.ndarray:
    """Apply Pauli correction U: rho -> U rho U^dagger."""
    return correction @ rho @ correction.conj().T


def density_close(rho1: np.ndarray, rho2: np.ndarray, tol: float = 1e-9) -> bool:
    return np.allclose(rho1, rho2, atol=tol)


def random_pure_state(seed: int = 0) -> np.ndarray:
    rng = np.random.default_rng(seed)
    v = rng.normal(size=2) + 1j * rng.normal(size=2)
    v = v / np.linalg.norm(v)
    return v


# --- gadget 1: Hadamard ----------------------------------------------------
# Paper's claim (theory.tex §"Hadamard gate"):
#   ancilla a in |+>
#   r1 := M_ZZ(q, a)
#   r2 := M_X(q)
#   if r1 == -1: frame_Z(a)
#   if r2 == -1: frame_X(a)
# expected: state on a equals H|psi>

def gadget_H_paper(psi: np.ndarray) -> dict:
    """Run paper's H gadget for input |psi> on qubit q, ancilla a in |+>.
    Returns per-branch results."""
    # qubit ordering: q is qubit 0, a is qubit 1
    plus = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    state = np.kron(psi, plus)
    ZZ = pauli_string_op("ZZ")
    XI = pauli_string_op("XI")  # X on q
    target_state = H_gate @ psi  # claimed final state on a
    target_rho = np.outer(target_state, target_state.conj())

    results = {}
    for r1 in (+1, -1):
        p1, s1 = measure(state, ZZ, r1)
        if p1 == 0:
            continue
        for r2 in (+1, -1):
            p2, s2 = measure(s1, XI, r2)
            if p2 == 0:
                continue
            # frame correction on a (qubit 1)
            corr = I.copy()
            if r1 == -1:
                corr = Z @ corr
            if r2 == -1:
                corr = X @ corr
            rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
            rho_a_corrected = state_after_correction(rho_a, corr)
            ok = density_close(rho_a_corrected, target_rho)
            results[(r1, r2)] = (p1 * p2, ok, rho_a_corrected)
    return results


# Alternative: maybe ancilla should be |0>? Try that variant too.
def gadget_H_alt_ancilla0(psi: np.ndarray) -> dict:
    zero = np.array([1, 0], dtype=complex)
    state = np.kron(psi, zero)
    ZZ = pauli_string_op("ZZ")
    XI = pauli_string_op("XI")
    target_state = H_gate @ psi
    target_rho = np.outer(target_state, target_state.conj())

    results = {}
    for r1 in (+1, -1):
        p1, s1 = measure(state, ZZ, r1)
        if p1 == 0:
            continue
        for r2 in (+1, -1):
            p2, s2 = measure(s1, XI, r2)
            if p2 == 0:
                continue
            corr = I.copy()
            if r1 == -1:
                corr = Z @ corr
            if r2 == -1:
                corr = X @ corr
            rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
            rho_a_corrected = state_after_correction(rho_a, corr)
            ok = density_close(rho_a_corrected, target_rho)
            results[(r1, r2)] = (p1 * p2, ok, rho_a_corrected)
    return results


# Standard textbook H gadget via single-qubit teleportation:
#   |+> ancilla, M_XX(q,a), M_Z(q), corrections X^r2 on a if r2=-1, Z^r1 if r1=-1
# This implements identity actually. The H gadget is usually:
#   ancilla |+>, M_ZX(q,a), M_X(q) — let's try.

def gadget_H_ZX_X(psi: np.ndarray) -> dict:
    """Try: M_{ZX}(q,a) then M_X(q), ancilla |+>. Claimed: H|psi> on a up to Pauli."""
    plus = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    state = np.kron(psi, plus)
    ZX = pauli_string_op("ZX")
    XI = pauli_string_op("XI")
    target_state = H_gate @ psi
    target_rho = np.outer(target_state, target_state.conj())

    results = {}
    for r1 in (+1, -1):
        p1, s1 = measure(state, ZX, r1)
        if p1 == 0:
            continue
        for r2 in (+1, -1):
            p2, s2 = measure(s1, XI, r2)
            if p2 == 0:
                continue
            # try both possible corrections; we report which works
            best = None
            for cz in (False, True):
                for cx in (False, True):
                    corr = I.copy()
                    if cz:
                        corr = Z @ corr
                    if cx:
                        corr = X @ corr
                    rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
                    rho_a_corrected = state_after_correction(rho_a, corr)
                    if density_close(rho_a_corrected, target_rho):
                        best = (cz, cx)
            results[(r1, r2)] = (p1 * p2, best)
    return results


def report_gadget(name: str, results: dict, mode: str = "verify"):
    print(f"\n=== {name} ===")
    if mode == "verify":
        all_ok = True
        for branch, (prob, ok, _rho) in results.items():
            tag = "OK" if ok else "FAIL"
            print(f"  branch {branch}  prob={prob:.4f}  {tag}")
            if not ok:
                all_ok = False
        print(f"  >>> {'PASS' if all_ok else 'FAIL'}")
    elif mode == "search":
        for branch, (prob, best) in results.items():
            print(f"  branch {branch}  prob={prob:.4f}  correction (Z?,X?)={best}")


# --- gadget 2: S (phase) ---------------------------------------------------
# Paper's claim:
#   r1 := M_YZ(q, a), r2 := M_X(q), corrections frame_Z(a) if r1=-1, frame_X(a) if r2=-1
#   ancilla |+>
#   expected: S|psi> on a

def gadget_S_paper(psi: np.ndarray) -> dict:
    plus = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    state = np.kron(psi, plus)
    YZ = pauli_string_op("YZ")
    XI = pauli_string_op("XI")
    target_state = S_gate @ psi
    target_rho = np.outer(target_state, target_state.conj())

    results = {}
    for r1 in (+1, -1):
        p1, s1 = measure(state, YZ, r1)
        if p1 == 0:
            continue
        for r2 in (+1, -1):
            p2, s2 = measure(s1, XI, r2)
            if p2 == 0:
                continue
            corr = I.copy()
            if r1 == -1:
                corr = Z @ corr
            if r2 == -1:
                corr = X @ corr
            rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
            rho_a_corrected = state_after_correction(rho_a, corr)
            ok = density_close(rho_a_corrected, target_rho)
            results[(r1, r2)] = (p1 * p2, ok, rho_a_corrected)
    return results


# search-mode S: try every Pauli correction set
def gadget_S_search(psi: np.ndarray, m1: str, m2_first_qubit: str, ancilla: str = "+") -> dict:
    """Generic 2-qubit-then-single-qubit search.
    m1: 2-qubit Pauli string for the first measurement (e.g. 'YZ', 'ZZ', 'YZ', 'XZ', 'ZY', 'ZX', etc.)
    m2_first_qubit: 'X', 'Y', or 'Z' applied to qubit q
    ancilla: '+' or '0'
    """
    if ancilla == "+":
        a_state = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    elif ancilla == "0":
        a_state = np.array([1, 0], dtype=complex)
    elif ancilla == "+i":
        a_state = (1 / np.sqrt(2)) * np.array([1, 1j], dtype=complex)
    else:
        raise ValueError(ancilla)
    state = np.kron(psi, a_state)
    M1 = pauli_string_op(m1)
    M2 = pauli_string_op(m2_first_qubit + "I")
    target_state = S_gate @ psi
    target_rho = np.outer(target_state, target_state.conj())

    results = {}
    for r1 in (+1, -1):
        p1, s1 = measure(state, M1, r1)
        if p1 == 0:
            continue
        for r2 in (+1, -1):
            p2, s2 = measure(s1, M2, r2)
            if p2 == 0:
                continue
            rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
            best = []
            for c in ("I", "X", "Y", "Z"):
                rho_a_c = state_after_correction(rho_a, PAULI[c])
                if density_close(rho_a_c, target_rho):
                    best.append(c)
            results[(r1, r2)] = (p1 * p2, best)
    return results


# --- gadget 3: CNOT --------------------------------------------------------
# Paper's claim (control c, target t, ancillas a1, a2 both |+>):
#   r1 := M_ZZ(c, a1)
#   r2 := M_XX(a1, t)
#   r3 := M_ZZ(a1, a2)
#   r4 := M_X(a1)
#   if r1 == -1: frame_Z(t)
#   if r2 == -1: frame_X(c)
#   if r3 == -1: frame_Z(c)
#   if r4 == -1: frame_X(t)

CNOT_mat = np.array(
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex
)


def gadget_CNOT_paper(psi_ct: np.ndarray) -> dict:
    """Input two-qubit state psi on (c, t).  Order: qubit 0=c, 1=t, 2=a1, 3=a2."""
    plus = (1 / np.sqrt(2)) * np.array([1, 1], dtype=complex)
    state = np.kron(np.kron(psi_ct, plus), plus)  # (c,t,a1,a2)

    # Build 4-qubit Pauli measurement operators
    def op4(s):
        return pauli_string_op(s)

    M1 = op4("ZIZI")  # ZZ on (c, a1)
    M2 = op4("IXXI")  # XX on (a1, t) — careful: a1 is qubit 2, t is qubit 1
    # Actually XX(a1, t) = X on a1 (qubit 2) tensor X on t (qubit 1)
    # So Pauli string at positions (c=0, t=1, a1=2, a2=3) = I X X I  ✓
    M3 = op4("IIZZ")  # ZZ on (a1, a2)
    M4 = op4("IIXI")  # X on a1

    target_state = CNOT_mat @ psi_ct
    target_rho_ct = np.outer(target_state, target_state.conj())

    results = {}
    for r1 in (+1, -1):
        p1, s1 = measure(state, M1, r1)
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
                for r4 in (+1, -1):
                    p4, s4 = measure(s3, M4, r4)
                    if p4 == 0:
                        continue
                    # frame corrections: build 2-qubit Pauli on (c, t)
                    corr_c = I.copy()
                    corr_t = I.copy()
                    if r1 == -1:
                        corr_t = Z @ corr_t
                    if r2 == -1:
                        corr_c = X @ corr_c
                    if r3 == -1:
                        corr_c = Z @ corr_c
                    if r4 == -1:
                        corr_t = X @ corr_t
                    corr_ct = np.kron(corr_c, corr_t)
                    # Reduce to (c, t) by tracing out a1, a2
                    rho_full = np.outer(s4, s4.conj()).reshape([2] * 8)
                    # axes: row indices 0..3 then col indices 4..7, qubits (c,t,a1,a2)
                    # trace out qubits 2,3 (a1, a2)
                    rho = np.einsum("ijklmnkl->ijmn", rho_full)
                    rho_ct = rho.reshape(4, 4)
                    rho_ct_corrected = state_after_correction(rho_ct, corr_ct)
                    ok = density_close(rho_ct_corrected, target_rho_ct)
                    results[(r1, r2, r3, r4)] = (p1 * p2 * p3 * p4, ok)
    return results


# --- main ------------------------------------------------------------------

def main():
    psi = random_pure_state(seed=42)
    print(f"Random input |psi> = {psi}")

    # H gadget — paper version
    res = gadget_H_paper(psi)
    report_gadget("H gadget (paper: M_ZZ; M_X; ancilla=|+>)", res)

    res = gadget_H_alt_ancilla0(psi)
    report_gadget("H gadget (M_ZZ; M_X; ancilla=|0>)", res)

    res = gadget_H_ZX_X(psi)
    report_gadget("H candidate (M_ZX; M_X; ancilla=|+>) — search", res, mode="search")

    # S gadget
    res = gadget_S_paper(psi)
    report_gadget("S gadget (paper: M_YZ; M_X; ancilla=|+>)", res)

    # broaden the search for S
    print("\n=== S gadget search variants ===")
    for m1 in ["YZ", "ZY", "YX", "XY"]:
        for m2 in ["X", "Y", "Z"]:
            for anc in ["+", "0", "+i"]:
                r = gadget_S_search(psi, m1, m2, anc)
                if all(best for (_p, best) in r.values()):
                    print(f"  works: M_{m1}; M_{m2}; ancilla=|{anc}>  branches: {{(r1,r2): correction}} =")
                    for k, (p, best) in r.items():
                        print(f"    {k} prob={p:.4f} valid corrections={best}")

    # CNOT gadget — random 2-qubit input
    rng = np.random.default_rng(7)
    v = rng.normal(size=4) + 1j * rng.normal(size=4)
    v = v / np.linalg.norm(v)
    print(f"\nRandom input |psi_ct> = {v}")
    res = gadget_CNOT_paper(v)
    n_ok = sum(1 for (_p, ok) in res.values() if ok)
    n_total = len(res)
    print(f"\n=== CNOT gadget (paper) ===")
    print(f"  branches passing: {n_ok}/{n_total}")
    if n_ok != n_total:
        print("  Failing branches:")
        for k, (p, ok) in res.items():
            if not ok:
                print(f"    {k} prob={p:.4f}")


if __name__ == "__main__":
    main()
