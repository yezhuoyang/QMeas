"""Numerically verify every Pauli-measurement optimization rule proved
in `lean/QMeas/Optimization.lean`.

For each rule we compute the LHS and RHS as concrete complex matrices
and assert equality (or application to random input states, when a
matrix identity is more convincing as a state-action identity).
"""

from __future__ import annotations
import numpy as np

I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)


def kron(A, B):
    return np.kron(A, B)


def projector(P, s: int):
    """(I + s * P) / 2."""
    d = P.shape[0]
    return 0.5 * (np.eye(d, dtype=complex) + s * P)


def assert_eq(name, LHS, RHS, tol=1e-12):
    ok = np.allclose(LHS, RHS, atol=tol)
    status = "PASS" if ok else "FAIL"
    print(f"  {status:4s}  {name}")
    if not ok:
        diff = np.max(np.abs(LHS - RHS))
        print(f"        max-abs difference: {diff:.3e}")
    return ok


def rule_idempotence():
    """Π_P^(s) * Π_P^(s) = Π_P^(s) for P in {Z, X} and s in {+1, -1}."""
    print("\n[1] Projector idempotence (measuring the same Pauli twice):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y")]:
        for s in (+1, -1):
            proj = projector(P, s)
            ok &= assert_eq(f"proj_{name}({s:+d})^2 = proj_{name}({s:+d})",
                            proj @ proj, proj)
    # Two-qubit XX, ZZ
    for P, name in [(kron(X, X), "XX"), (kron(Z, Z), "ZZ"), (kron(Z, X), "ZX")]:
        for s in (+1, -1):
            proj = projector(P, s)
            ok &= assert_eq(f"proj_{name}({s:+d})^2 = proj_{name}({s:+d})",
                            proj @ proj, proj)
    return ok


def rule_orthogonality():
    """Π_P^(+1) * Π_P^(-1) = 0."""
    print("\n[2] Projector orthogonality (opposite outcomes are disjoint):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y"),
                     (kron(X, X), "XX"), (kron(Z, Z), "ZZ"), (kron(Z, X), "ZX")]:
        d = P.shape[0]
        ok &= assert_eq(f"proj_{name}(+1) * proj_{name}(-1) = 0",
                        projector(P, +1) @ projector(P, -1),
                        np.zeros((d, d), dtype=complex))
    return ok


def rule_completeness():
    """Π_P^(+1) + Π_P^(-1) = I."""
    print("\n[3] Projector sum = I (completeness of spectral decomp):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y"),
                     (kron(X, X), "XX"), (kron(Z, Z), "ZZ"), (kron(Z, X), "ZX")]:
        d = P.shape[0]
        ok &= assert_eq(f"proj_{name}(+1) + proj_{name}(-1) = I",
                        projector(P, +1) + projector(P, -1),
                        np.eye(d, dtype=complex))
    return ok


def rule_commuting_measurements():
    """If [P, Q] = 0, then Π_P^(s) Π_Q^(t) = Π_Q^(t) Π_P^(s).

    Consequence: the two measurements can be run in parallel, saving up
    to d QEC rounds per reordering on a surface-code back-end."""
    print("\n[4] Commuting-measurement reordering (enables parallelization):")
    ok = True
    pairs = [
        ("XX", kron(X, X), "ZZ", kron(Z, Z)),
        ("ZI", kron(Z, I), "IX", kron(I, X)),
        ("ZZ", kron(Z, Z), "ZZ", kron(Z, Z)),  # same-op commutes (idem)
        ("ZI", kron(Z, I), "ZZ", kron(Z, Z)),  # share a Z on qubit 0
    ]
    for nP, P, nQ, Q in pairs:
        comm = P @ Q - Q @ P
        if not np.allclose(comm, 0, atol=1e-12):
            print(f"  skip  {nP} and {nQ} do NOT commute (not a parallelizable pair)")
            continue
        for s in (+1, -1):
            for t in (+1, -1):
                ok &= assert_eq(
                    f"proj_{nP}({s:+d}) proj_{nQ}({t:+d}) = proj_{nQ}({t:+d}) proj_{nP}({s:+d})",
                    projector(P, s) @ projector(Q, t),
                    projector(Q, t) @ projector(P, s))
    return ok


def rule_frame_absorption():
    """{P, Q} = 0 (anticommute): Q Π_P^(s) = Π_P^(-s) Q.

    A frame Pauli Q standing before a measurement M_P can be absorbed:
    the physical measurement stays; only the recorded outcome is
    classically flipped."""
    print("\n[5] Frame absorption via anticommutation (sign flip, zero cost):")
    ok = True
    for nP, P, nQ, Q in [("Z", Z, "X", X), ("X", X, "Z", Z), ("Z", Z, "Y", Y), ("X", X, "Y", Y), ("Y", Y, "X", X), ("Y", Y, "Z", Z)]:
        # anticommute check
        ac = P @ Q + Q @ P
        if not np.allclose(ac, 0, atol=1e-12):
            print(f"  skip  {nP} and {nQ} do not anticommute")
            continue
        for s in (+1, -1):
            ok &= assert_eq(
                f"{nQ} * proj_{nP}({s:+d}) = proj_{nP}({-s:+d}) * {nQ}",
                Q @ projector(P, s),
                projector(P, -s) @ Q)
    return ok


def rule_depth_reduction_example():
    """Given a random program of k commuting measurements on disjoint
    qubits, check that executing them sequentially vs. simultaneously
    (i.e., via the product of projectors in either order) yields the
    same final state."""
    print("\n[6] Depth reduction via parallelization (example, 3 disjoint meas):")
    rng = np.random.default_rng(42)
    # 3 qubits; M_Z on qubit 0, M_X on qubit 1, M_Y on qubit 2 -> all disjoint
    Z0 = kron(kron(Z, I), I)
    X1 = kron(kron(I, X), I)
    Y2 = kron(kron(I, I), Y)
    # random input
    v = rng.normal(size=8) + 1j * rng.normal(size=8)
    v /= np.linalg.norm(v)
    ok = True
    for s0 in (+1, -1):
        for s1 in (+1, -1):
            for s2 in (+1, -1):
                P0, P1, P2 = projector(Z0, s0), projector(X1, s1), projector(Y2, s2)
                # All 6 orderings
                orders = [
                    P0 @ P1 @ P2, P0 @ P2 @ P1,
                    P1 @ P0 @ P2, P1 @ P2 @ P0,
                    P2 @ P0 @ P1, P2 @ P1 @ P0,
                ]
                ref = orders[0] @ v
                for k, op in enumerate(orders[1:], start=1):
                    ok &= assert_eq(
                        f"branch ({s0:+d},{s1:+d},{s2:+d}) order#{k} consistent",
                        op @ v, ref)
    return ok


def rule_measurement_idempotent_on_states():
    """Operational: M_P(q); M_P(q) on a fresh input state — the second
    outcome matches the first with probability 1 (no physical measurement
    is needed for the second)."""
    print("\n[7] Operational idempotence (state-level):")
    rng = np.random.default_rng(5)
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (kron(Z, Z), "ZZ")]:
        d = P.shape[0]
        for _ in range(10):
            v = rng.normal(size=d) + 1j * rng.normal(size=d)
            v /= np.linalg.norm(v)
            for s in (+1, -1):
                proj = projector(P, s)
                # Post-meas state in s-branch (unnormalized)
                post = proj @ v
                # Second measurement with outcome s: proj @ post = post
                # Second measurement with outcome -s: (1 - proj) @ post = 0
                if np.linalg.norm(post) < 1e-12:
                    continue  # probability-0 branch
                ok &= np.allclose(proj @ post, post, atol=1e-10)
                ok &= np.allclose(projector(P, -s) @ post, 0, atol=1e-10)
        print(f"  {'PASS' if ok else 'FAIL':4s}  M_{name}; M_{name} is operationally idempotent on 10 random inputs × 2 outcomes")
    return ok


def main():
    print("Verifying Pauli-measurement optimization rules")
    print("(mirroring theorems in lean/QMeas/Optimization.lean)")
    print("-" * 60)
    results = [
        rule_idempotence(),
        rule_orthogonality(),
        rule_completeness(),
        rule_commuting_measurements(),
        rule_frame_absorption(),
        rule_depth_reduction_example(),
        rule_measurement_idempotent_on_states(),
    ]
    print()
    n_pass = sum(1 for r in results if r)
    print(f"RESULT: {n_pass}/{len(results)} rule families pass.")


if __name__ == "__main__":
    main()
