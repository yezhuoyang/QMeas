"""Cross-check the Lean theorem statements against numerical Qiskit simulation.

For each branch lemma in `lean/QMeas/Gadgets/{H,S,CNOT}.lean`, we compute the
post-measurement state as in Lean (the explicit `state_*` definition), apply
the Lean correction, and verify equality with the unitary action (up to the
documented global phase, if any) on random inputs.

This serves as a safety net: if the Lean theorem statement disagrees with
physics, the discrepancy will surface here even if the Lean proof goes
through (because the Lean proof is purely algebraic).
"""

from __future__ import annotations
import numpy as np

from validate_gadgets import (
    I, X, Y, Z, H_gate, S_gate, PAULI, pauli_string_op,
    measure, reduce_to_qubit, density_close,
)


# ---- Lean-mirrored state definitions ------------------------------------

def lean_psi(alpha, beta):
    return np.array([alpha, beta], dtype=complex)


# H gadget (|0> ancilla, M_ZX + M_X)
def lean_state_a_H_pp(a, b):
    return np.array([(a + b), (a - b)], dtype=complex) / np.sqrt(2)

def lean_state_a_H_pm(a, b):
    return np.array([(a - b), (a + b)], dtype=complex) / np.sqrt(2)

def lean_state_a_H_mp(a, b):
    return np.array([(a + b), -(a - b)], dtype=complex) / np.sqrt(2)

def lean_state_a_H_mm(a, b):
    return np.array([-(a - b), (a + b)], dtype=complex) / np.sqrt(2)


# S gadget (|+> ancilla, M_ZZ + M_Y)
def lean_state_a_S_pp(a, b):
    return np.array([a, -1j * b], dtype=complex)

def lean_state_a_S_pm(a, b):
    return np.array([a, 1j * b], dtype=complex)

def lean_state_a_S_mp(a, b):
    return np.array([-1j * b, a], dtype=complex)

def lean_state_a_S_mm(a, b):
    return np.array([1j * b, a], dtype=complex)


# CNOT gadget (|+> ancilla, M_ZZ(c,a); M_XX(a,t); M_Z(a))
def lean_state_CNOT(branch, a):
    a0, a1, a2, a3 = a
    table = {
        "ppp": [a0, a1, a3, a2],
        "ppm": [a1, a0, a2, a3],
        "pmp": [a0, a1, -a3, -a2],
        "pmm": [-a1, -a0, a2, a3],
        "mpp": [a1, a0, a2, a3],
        "mpm": [a0, a1, a3, a2],
        "mmp": [-a1, -a0, a2, a3],
        "mmm": [a0, a1, -a3, -a2],
    }
    return np.array(table[branch], dtype=complex)


CNOT_mat = np.array(
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex
)


def vec_close(u, v, tol=1e-10):
    return np.allclose(u, v, atol=tol)


# ---- Cross-checks --------------------------------------------------------

def check_H():
    print("=== H gadget Lean theorems vs unitary H ===")
    rng = np.random.default_rng(0)
    fails = 0
    for k in range(20):
        v = rng.normal(size=2) + 1j * rng.normal(size=2)
        v /= np.linalg.norm(v)
        a, b = v
        target = H_gate @ np.array([a, b])
        checks = [
            ("(+,+) no corr",      lean_state_a_H_pp(a, b),       target,                 1.0),
            ("(+,-) X corr",       X @ lean_state_a_H_pm(a, b),   target,                 1.0),
            ("(-,+) Z corr",       Z @ lean_state_a_H_mp(a, b),   target,                 1.0),
            ("(-,-) Y corr",       Y @ lean_state_a_H_mm(a, b),   target,                -1j),
        ]
        for name, lhs, rhs, phase in checks:
            ok = vec_close(lhs, phase * rhs)
            if not ok:
                fails += 1
                print(f"  seed {k} {name}  FAIL")
    print(f"  {'PASS' if fails == 0 else f'FAIL ({fails})'}  (20 random seeds × 4 branches)")


def check_S():
    print("\n=== S gadget Lean theorems vs unitary S ===")
    rng = np.random.default_rng(1)
    fails = 0
    for k in range(20):
        v = rng.normal(size=2) + 1j * rng.normal(size=2)
        v /= np.linalg.norm(v)
        a, b = v
        target = S_gate @ np.array([a, b])
        checks = [
            ("(+,+) Z corr",       Z @ lean_state_a_S_pp(a, b),   target,                 1.0),
            ("(+,-) no corr",      lean_state_a_S_pm(a, b),       target,                 1.0),
            ("(-,+) Y corr",       Y @ lean_state_a_S_mp(a, b),   target,                -1j),
            ("(-,-) X corr",       X @ lean_state_a_S_mm(a, b),   target,                 1.0),
        ]
        for name, lhs, rhs, phase in checks:
            ok = vec_close(lhs, phase * rhs)
            if not ok:
                fails += 1
                print(f"  seed {k} {name}  FAIL")
    print(f"  {'PASS' if fails == 0 else f'FAIL ({fails})'}  (20 random seeds × 4 branches)")


def check_CNOT():
    print("\n=== CNOT gadget Lean theorems vs unitary CNOT ===")
    rng = np.random.default_rng(2)
    fails = 0
    II = np.eye(4, dtype=complex)
    IX = np.kron(I, X)
    ZI = np.kron(Z, I)
    ZX = np.kron(Z, X)
    for k in range(20):
        a = rng.normal(size=4) + 1j * rng.normal(size=4)
        a /= np.linalg.norm(a)
        target = CNOT_mat @ a
        checks = [
            ("(+,+,+) II",     II @ lean_state_CNOT("ppp", a),  target,  1.0),
            ("(+,+,-) IX",     IX @ lean_state_CNOT("ppm", a),  target,  1.0),
            ("(+,-,+) ZI",     ZI @ lean_state_CNOT("pmp", a),  target,  1.0),
            ("(+,-,-) ZX",     ZX @ lean_state_CNOT("pmm", a),  target, -1.0),
            ("(-,+,+) IX",     IX @ lean_state_CNOT("mpp", a),  target,  1.0),
            ("(-,+,-) II",     II @ lean_state_CNOT("mpm", a),  target,  1.0),
            ("(-,-,+) ZX",     ZX @ lean_state_CNOT("mmp", a),  target, -1.0),
            ("(-,-,-) ZI",     ZI @ lean_state_CNOT("mmm", a),  target,  1.0),
        ]
        for name, lhs, rhs, phase in checks:
            ok = vec_close(lhs, phase * rhs)
            if not ok:
                fails += 1
                print(f"  seed {k} {name}  FAIL  lhs={lhs} expected={phase * rhs}")
    print(f"  {'PASS' if fails == 0 else f'FAIL ({fails})'}  (20 random seeds × 8 branches)")


# ---- Also re-validate that the Lean state matches the actual quantum simulation
# for the input/output gadget program (full Qiskit measurement loop)

def check_H_simulation_matches_lean():
    """Confirm the Lean `state_a_*` actually equals the post-measurement state
    obtained by simulating the gadget."""
    print("\n=== H gadget: Lean state defs match Qiskit simulation ===")
    rng = np.random.default_rng(3)
    fails = 0
    zero = np.array([1, 0], dtype=complex)
    ZX_op = pauli_string_op("ZX")
    XI_op = pauli_string_op("XI")
    for k in range(10):
        v = rng.normal(size=2) + 1j * rng.normal(size=2)
        v /= np.linalg.norm(v)
        a, b = v
        joint = np.kron(v, zero)
        for r1 in (+1, -1):
            p1, s1 = measure(joint, ZX_op, r1)
            if p1 == 0: continue
            for r2 in (+1, -1):
                p2, s2 = measure(s1, XI_op, r2)
                if p2 == 0: continue
                # state on qubit 1 (a)
                rho_a = reduce_to_qubit(s2, n_qubits=2, target=1)
                if r1 == +1 and r2 == +1:
                    pred = lean_state_a_H_pp(a, b)
                elif r1 == +1 and r2 == -1:
                    pred = lean_state_a_H_pm(a, b)
                elif r1 == -1 and r2 == +1:
                    pred = lean_state_a_H_mp(a, b)
                else:
                    pred = lean_state_a_H_mm(a, b)
                rho_pred = np.outer(pred, pred.conj())
                if not density_close(rho_a, rho_pred):
                    fails += 1
                    print(f"  seed {k}, branch ({r1:+d},{r2:+d}) MISMATCH")
    print(f"  {'PASS' if fails == 0 else f'FAIL ({fails})'}")


if __name__ == "__main__":
    print("Cross-checking Lean theorem statements against Qiskit numerics.")
    print("-" * 60)
    check_H()
    check_S()
    check_CNOT()
    check_H_simulation_matches_lean()
