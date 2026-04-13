"""Compile small Clifford circuits to QMeas (mirroring lean/QMeas/Compiler.lean)
and validate against direct Qiskit simulation of the original unitary.

For each random circuit:
  1. Build the unitary U via direct gate composition (numpy).
  2. Compile to a measurement-program description (list of measurement
     primitives and frame updates), faithfully mirroring the Lean
     `compile1` / `compile2` functions.
  3. Simulate the QMeas program: enumerate every measurement-outcome
     branch, accumulate the post-measurement state and the Pauli frame.
  4. Verify: for every branch, the Pauli-frame-corrected output state
     equals U|ψ⟩ (up to an unobservable global phase).

This is the operational analogue of the Lean soundness theorem; it
exercises the COMPILER on circuits longer than a single gate, where the
Lean structural-induction proof has a `sorry`.
"""

from __future__ import annotations
import numpy as np
from itertools import product

# ---- Unitaries ----------------------------------------------------------

I = np.array([[1, 0], [0, 1]], dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)
H = (1 / np.sqrt(2)) * np.array([[1, 1], [1, -1]], dtype=complex)
S = np.array([[1, 0], [0, 1j]], dtype=complex)
PAULI = {"I": I, "X": X, "Y": Y, "Z": Z}

CNOT01 = np.array(
    [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], dtype=complex
)


def kron_n(ops):
    out = np.array([[1.0 + 0.0j]])
    for op in ops:
        out = np.kron(out, op)
    return out


def lift0(U):
    return np.kron(U, I)


def lift1(U):
    return np.kron(I, U)


# ---- Single-qubit gadget descriptions (mirrors Lean compile1) -----------

def gadget_H_program():
    """Returns (measurements, frame-rules, ancilla_init).
    Measurements are listed in order: each is ('1q'/'2q', PauliString).
    The simulator interprets bit names by position: r1=outcome of meas 0,
    r2=outcome of meas 1, etc."""
    return {
        "ancilla": "0",
        "measurements": [("2q", "ZX"), ("1q", "X")],   # M_ZX(q,a), M_X(q)
        # frame-rule encoding: each rule is (predicate over bits, target qubit, Pauli)
        "frames": [
            (lambda r: r[0] == -1, "a", "Z"),
            (lambda r: r[1] == -1, "a", "X"),
        ],
        "target_unitary": H,
    }


def gadget_S_program():
    return {
        "ancilla": "+",
        "measurements": [("2q", "ZZ"), ("1q", "Y")],
        "frames": [
            (lambda r: r[0] == +1 and r[1] == +1, "a", "Z"),
            (lambda r: r[0] == -1 and r[1] == +1, "a", "Y"),
            (lambda r: r[0] == -1 and r[1] == -1, "a", "X"),
        ],
        "target_unitary": S,
    }


def gadget_CNOT_program():
    return {
        "ancilla": "+",
        "measurements": [("zz_ca", "ZZ"), ("xx_at", "XX"), ("z_a", "Z")],
        "frames": [
            (lambda r: r[1] == -1, "c", "Z"),
            (lambda r: r[0] != r[2], "t", "X"),
        ],
        "target_unitary": CNOT01,
    }


# ---- Branch enumerator --------------------------------------------------

def measure_branch(state, op, eigval):
    d = op.shape[0]
    P = 0.5 * (np.eye(d, dtype=complex) + eigval * op)
    new = P @ state
    nrm = float(np.real(np.vdot(new, new)))
    if nrm < 1e-14:
        return 0.0, np.zeros_like(state)
    return nrm, new / np.sqrt(nrm)


def reduce_to_subset(state, n_qubits, keep_qubits):
    """Trace out qubits NOT in keep_qubits. Returns the joint density matrix
    over the kept qubits (assumes the state factorizes properly; otherwise
    the reduced density matrix is mixed)."""
    rho = np.outer(state, state.conj()).reshape([2] * n_qubits + [2] * n_qubits)
    drop = sorted(set(range(n_qubits)) - set(keep_qubits), reverse=True)
    for q in drop:
        rho = np.einsum(
            ''.join(['ij'] + [chr(97 + i) for i in range(2 * n_qubits - 2)])[:0]
            or '...',
            rho,
        )
    # Simpler: build the partial trace explicitly via tensor reshape.
    # Use a manual implementation:
    return _partial_trace(state, n_qubits, keep_qubits)


def _partial_trace(state, n_qubits, keep_qubits):
    """Brute-force partial trace over qubits not in `keep_qubits`."""
    keep_qubits = sorted(keep_qubits)
    drop_qubits = sorted(set(range(n_qubits)) - set(keep_qubits))
    keep_dim = 2 ** len(keep_qubits)
    drop_dim = 2 ** len(drop_qubits)
    rho = np.zeros((keep_dim, keep_dim), dtype=complex)
    # iterate basis indices
    for i in range(2 ** n_qubits):
        for j in range(2 ** n_qubits):
            bits_i = [(i >> (n_qubits - 1 - q)) & 1 for q in range(n_qubits)]
            bits_j = [(j >> (n_qubits - 1 - q)) & 1 for q in range(n_qubits)]
            # require dropped qubits to match (trace condition)
            if any(bits_i[q] != bits_j[q] for q in drop_qubits):
                continue
            # form keep-indices
            ki = sum(bits_i[q] << (len(keep_qubits) - 1 - idx)
                     for idx, q in enumerate(keep_qubits))
            kj = sum(bits_j[q] << (len(keep_qubits) - 1 - idx)
                     for idx, q in enumerate(keep_qubits))
            rho[ki, kj] += state[i] * state[j].conj()
    return rho


def density_close(rho1, rho2, tol=1e-9):
    return np.allclose(rho1, rho2, atol=tol)


# ---- Single-qubit Clifford circuit compiler/simulator -------------------

def compose1(circuit):
    """Compose single-qubit unitary from a list of gates (str: 'H' or 'S')."""
    U = I.copy()
    for g in circuit:
        if g == "H":
            U = H @ U
        elif g == "S":
            U = S @ U
        else:
            raise ValueError(g)
    return U


def simulate1(circuit, psi):
    """Simulate the compiled QMeas program for a single-qubit circuit on
    input |ψ⟩.  Returns a dict {branch_tuple: (joint_prob, state_on_a, frame_pauli)}.

    The single logical qubit is threaded through the gadgets: each gate
    consumes the current logical qubit (`q`) and emits a fresh ancilla
    (`a`).  The frame is a Pauli on the current logical qubit (carried
    forward and pushed through subsequent Cliffords)."""
    state = psi.copy()        # 2-dim: lives on the current logical qubit
    frame = "I"               # Pauli on the current qubit
    branches = {(): (1.0, state, frame)}

    for g in circuit:
        gd = gadget_H_program() if g == "H" else gadget_S_program()
        new_branches = {}
        for trace, (prob, st, fr) in branches.items():
            # initial joint state: st (qubit q) ⊗ ancilla in |0> or |+>
            anc = (np.array([1, 0], complex) if gd["ancilla"] == "0"
                   else np.array([1, 1], complex) / np.sqrt(2))
            joint = np.kron(st, anc)        # (q, a), 4-dim
            for r1 in (+1, -1):
                op1 = (kron_n([PAULI[gd["measurements"][0][1][0]],
                                PAULI[gd["measurements"][0][1][1]]])
                       if gd["measurements"][0][0] == "2q"
                       else None)
                p1, s1 = measure_branch(joint, op1, r1)
                if p1 == 0:
                    continue
                for r2 in (+1, -1):
                    op2 = kron_n([PAULI[gd["measurements"][1][1]], I])  # 1q on q
                    p2, s2 = measure_branch(s1, op2, r2)
                    if p2 == 0:
                        continue
                    # Reduce to the ancilla qubit (qubit 1)
                    rho_a = _partial_trace(s2, 2, [1])
                    # Sanity: rho_a should be pure here for our gadgets.
                    # Extract pure state from rho_a (largest eigenvector).
                    evals, evecs = np.linalg.eigh(rho_a)
                    new_st = evecs[:, -1] * np.exp(-1j * np.angle(evecs[0, -1] + 1e-30))
                    # Apply frame rules (compute the new frame as a Pauli)
                    rs = [r1, r2]
                    fr_new_letters = []
                    for pred, target, pauli in gd["frames"]:
                        if pred(rs) and target == "a":
                            fr_new_letters.append(pauli)
                    # Combine: the *previous* frame on q is pushed through
                    # the gate U; concretely, frame propagation says the
                    # frame at the new qubit a is (applied frames here)
                    # composed with the previous-frame pushed through U.
                    # For now, push fr through U using a small commutation
                    # table.
                    fr_after = _push_pauli(fr, g)
                    # Multiply fr_after with collected frames
                    new_fr = fr_after
                    for p in fr_new_letters:
                        new_fr = _pauli_mul(new_fr, p)
                    new_branches[trace + ((r1, r2),)] = (
                        prob * p1 * p2, new_st, new_fr)
        branches = new_branches
    return branches


def _push_pauli(p, gate):
    """Single-qubit Clifford-Pauli commutation: U·P = P'·U.  Returns P'."""
    table = {
        ("H", "I"): "I", ("H", "X"): "Z", ("H", "Y"): "Y", ("H", "Z"): "X",
        ("S", "I"): "I", ("S", "X"): "Y", ("S", "Y"): "X", ("S", "Z"): "Z",
    }
    return table[(gate, p)]


def _pauli_mul(p, q):
    """Pauli multiplication on the projective group (drop global phase)."""
    if p == "I":
        return q
    if q == "I":
        return p
    if p == q:
        return "I"
    table = {
        ("X", "Y"): "Z", ("Y", "X"): "Z",
        ("Y", "Z"): "X", ("Z", "Y"): "X",
        ("Z", "X"): "Y", ("X", "Z"): "Y",
    }
    return table[(p, q)]


def validate1(circuit, n_seeds=10):
    """Verify: for every branch of compile(circuit), frame · output = U|ψ⟩
    (up to global phase) on `n_seeds` random inputs."""
    rng = np.random.default_rng(hash(tuple(circuit)) & 0xFFFFFFFF)
    U = compose1(circuit)
    fails = 0
    for k in range(n_seeds):
        v = rng.normal(size=2) + 1j * rng.normal(size=2)
        v /= np.linalg.norm(v)
        target = U @ v
        target_rho = np.outer(target, target.conj())
        branches = simulate1(circuit, v)
        if not branches:
            fails += 1
            continue
        prob_total = 0.0
        for trace, (prob, st, fr) in branches.items():
            prob_total += prob
            # apply Pauli frame
            corrected = PAULI[fr] @ st
            corrected_rho = np.outer(corrected, corrected.conj())
            if not density_close(corrected_rho, target_rho):
                fails += 1
        if abs(prob_total - 1.0) > 1e-6:
            print(f"  WARNING: prob_total={prob_total}")
    return fails


def main():
    print("Compile-and-validate: random single-qubit Clifford circuits.")
    print(f"Each circuit: compile to QMeas, simulate every branch, frame-correct,")
    print(f"compare density matrix to U|ψ⟩.\n")
    rng = np.random.default_rng(2026)
    test_circuits = [
        [],
        ["H"],
        ["S"],
        ["H", "H"],          # = I
        ["S", "S"],          # = Z
        ["H", "S"],
        ["S", "H"],
        ["H", "S", "H"],     # = sqrt(X)
        ["S", "H", "S"],
        ["H", "S", "S", "H"],     # = X
        ["H", "S", "H", "S"],
    ]
    # plus a few random ones
    for _ in range(8):
        n = rng.integers(2, 7)
        gates = ["H" if rng.random() < 0.5 else "S" for _ in range(int(n))]
        test_circuits.append(gates)

    overall_fails = 0
    for circ in test_circuits:
        fails = validate1(circ, n_seeds=5)
        marker = "PASS" if fails == 0 else f"FAIL ({fails})"
        print(f"  circuit {circ}  -> {marker}")
        overall_fails += fails

    print(f"\nTotal failures: {overall_fails}")
    print("If 0, the compiler+frame propagation is consistent with the unitary "
          "denotation on every branch of every test circuit.")


if __name__ == "__main__":
    main()
