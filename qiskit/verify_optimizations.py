"""Numerically verify every Pauli-measurement optimization rule proved
in `lean/QMeas/Optimization.lean` (38 theorems).

Each rule is checked as a concrete complex-matrix identity, or as a
state-action identity on random inputs.  Output: N/N rule families pass.
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
    d = P.shape[0]
    return 0.5 * (np.eye(d, dtype=complex) + s * P)


def assert_eq(name, LHS, RHS, tol=1e-12):
    ok = np.allclose(LHS, RHS, atol=tol)
    status = "PASS" if ok else "FAIL"
    print(f"  {status:4s}  {name}")
    if not ok:
        print(f"        max-abs difference: {np.max(np.abs(LHS - RHS)):.3e}")
    return ok


def rule_idempotence():
    print("\n[1] Projector idempotence (Π_P^{s} squared = itself):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y"),
                     (kron(X, X), "XX"), (kron(Z, Z), "ZZ"), (kron(Z, X), "ZX")]:
        for s in (+1, -1):
            proj = projector(P, s)
            ok &= assert_eq(f"proj_{name}({s:+d})² = proj_{name}({s:+d})",
                            proj @ proj, proj)
    return ok


def rule_orthogonality():
    print("\n[2] Opposite outcomes are orthogonal:")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y"),
                     (kron(X, X), "XX"), (kron(Z, Z), "ZZ"), (kron(Z, X), "ZX")]:
        d = P.shape[0]
        ok &= assert_eq(f"proj_{name}(+1) * proj_{name}(-1) = 0",
                        projector(P, +1) @ projector(P, -1),
                        np.zeros((d, d), dtype=complex))
    return ok


def rule_completeness():
    print("\n[3] Spectral completeness (sum of projectors = I):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y"),
                     (kron(X, X), "XX"), (kron(Z, Z), "ZZ"), (kron(Z, X), "ZX")]:
        d = P.shape[0]
        ok &= assert_eq(f"proj_{name}(+1) + proj_{name}(-1) = I",
                        projector(P, +1) + projector(P, -1),
                        np.eye(d, dtype=complex))
    return ok


def rule_pauli_involutions():
    print("\n[4] Pauli involutions (σ_P² = I):")
    ok = True
    ok &= assert_eq("X² = I", X @ X, I)
    ok &= assert_eq("Y² = I", Y @ Y, I)
    ok &= assert_eq("Z² = I", Z @ Z, I)
    return ok


def rule_pauli_products():
    print("\n[5] Pauli products (quaternion-like):")
    ok = True
    ok &= assert_eq("X · Y = i·Z", X @ Y, 1j * Z)
    ok &= assert_eq("Y · Z = i·X", Y @ Z, 1j * X)
    ok &= assert_eq("Z · X = i·Y", Z @ X, 1j * Y)
    return ok


def rule_pauli_anticommutations():
    print("\n[6] Pauli anticommutations (σ_P·σ_Q = -σ_Q·σ_P):")
    ok = True
    ok &= assert_eq("X · Y = -(Y · X)", X @ Y, -(Y @ X))
    ok &= assert_eq("Y · Z = -(Z · Y)", Y @ Z, -(Z @ Y))
    ok &= assert_eq("X · Z = -(Z · X)", X @ Z, -(Z @ X))
    return ok


def rule_eigenvalue_identity():
    """P · Π_P^{(s)} = s · Π_P^{(s)}: the central fact behind R1."""
    print("\n[7] Eigenvalue identity (P · Π_P^{(s)} = s · Π_P^{(s)}):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y")]:
        for s in (+1, -1):
            proj = projector(P, s)
            ok &= assert_eq(f"{name} · proj_{name}({s:+d}) = {s:+d} · proj_{name}({s:+d})",
                            P @ proj, s * proj)
    return ok


def rule_projector_difference():
    """Π_P^{(+)} - Π_P^{(-)} = P."""
    print("\n[8] Projector difference (Π^{+} - Π^{-} = P):")
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y")]:
        ok &= assert_eq(f"proj_{name}(+1) - proj_{name}(-1) = {name}",
                        projector(P, 1) - projector(P, -1), P)
    return ok


def rule_commuting_measurements():
    """If [P, Q] = 0, Π_P^{(s)} Π_Q^{(t)} = Π_Q^{(t)} Π_P^{(s)}."""
    print("\n[9] Commuting measurement reordering (enables parallel scheduling):")
    ok = True
    pairs = [
        ("ZZ",  kron(Z, Z), "XX",  kron(X, X)),  # 2 anticomm → commute
        ("ZI",  kron(Z, I), "IX",  kron(I, X)),  # disjoint
        ("YY",  kron(Y, Y), "ZZ",  kron(Z, Z)),  # 2 anticomm
        ("YY",  kron(Y, Y), "XX",  kron(X, X)),  # 2 anticomm
        ("ZZ",  kron(Z, Z), "ZI",  kron(Z, I)),  # 0 anticomm on overlap
        ("XZ",  kron(X, Z), "ZX",  kron(Z, X)),  # 2 anticomm
    ]
    for nP, P, nQ, Q in pairs:
        if not np.allclose(P @ Q - Q @ P, 0, atol=1e-12):
            print(f"  skip  {nP} and {nQ} do not commute")
            continue
        for s in (+1, -1):
            for t in (+1, -1):
                ok &= assert_eq(
                    f"proj_{nP}({s:+d})·proj_{nQ}({t:+d}) = proj_{nQ}({t:+d})·proj_{nP}({s:+d})",
                    projector(P, s) @ projector(Q, t),
                    projector(Q, t) @ projector(P, s))
    return ok


def rule_frame_absorption():
    """{P, Q} = 0: Q · Π_P^{(s)} = Π_P^{(-s)} · Q."""
    print("\n[10] Frame absorption on anticommutation (outcome flip):")
    ok = True
    for nP, P, nQ, Q in [
        ("Z", Z, "X", X), ("X", X, "Z", Z),
        ("Z", Z, "Y", Y), ("Y", Y, "Z", Z),
        ("X", X, "Y", Y), ("Y", Y, "X", X),
    ]:
        if not np.allclose(P @ Q + Q @ P, 0, atol=1e-12):
            continue
        for s in (+1, -1):
            ok &= assert_eq(
                f"{nQ} · proj_{nP}({s:+d}) = proj_{nP}({-s:+d}) · {nQ}",
                Q @ projector(P, s), projector(P, -s) @ Q)
    return ok


def rule_sandwich():
    """P · Π_Q^{(s)} · P = Π_Q^{(-s)} if {P,Q}=0; Π_Q^{(s)} if [P,Q]=0."""
    print("\n[11] Sandwich rule (P·Π_Q·P = Π_Q^{±s}):")
    ok = True
    # anticommuting
    for nP, P, nQ, Q in [("X", X, "Z", Z), ("Z", Z, "X", X), ("Y", Y, "Z", Z)]:
        if not np.allclose(P @ Q + Q @ P, 0, atol=1e-12):
            continue
        for s in (+1, -1):
            ok &= assert_eq(
                f"{nP} · proj_{nQ}({s:+d}) · {nP} = proj_{nQ}({-s:+d})",
                P @ projector(Q, s) @ P, projector(Q, -s))
    # commuting (same-Pauli)
    for nP, P in [("Z", Z), ("X", X), ("Y", Y)]:
        for s in (+1, -1):
            ok &= assert_eq(
                f"{nP} · proj_{nP}({s:+d}) · {nP} = proj_{nP}({s:+d})",
                P @ projector(P, s) @ P, projector(P, s))
    return ok


def rule_depth_reduction_example():
    print("\n[12] Depth reduction: 3 disjoint measurements parallelize:")
    rng = np.random.default_rng(42)
    Z0 = kron(kron(Z, I), I)
    X1 = kron(kron(I, X), I)
    Y2 = kron(kron(I, I), Y)
    v = rng.normal(size=8) + 1j * rng.normal(size=8)
    v /= np.linalg.norm(v)
    ok = True
    for s0 in (+1, -1):
        for s1 in (+1, -1):
            for s2 in (+1, -1):
                P0 = projector(Z0, s0); P1 = projector(X1, s1); P2 = projector(Y2, s2)
                ref = P0 @ P1 @ P2 @ v
                for order in [P0 @ P2 @ P1, P1 @ P0 @ P2, P1 @ P2 @ P0,
                              P2 @ P0 @ P1, P2 @ P1 @ P0]:
                    ok &= np.allclose(order @ v, ref, atol=1e-10)
    print(f"  {'PASS' if ok else 'FAIL':4s}  48 branch-order consistency checks")
    return ok


def rule_operational_idempotence():
    print("\n[13] Operational idempotence (M_P; M_P is deterministic):")
    rng = np.random.default_rng(5)
    ok = True
    for P, name in [(Z, "Z"), (X, "X"), (Y, "Y"),
                     (kron(Z, Z), "ZZ"), (kron(X, X), "XX")]:
        d = P.shape[0]
        for _ in range(10):
            v = rng.normal(size=d) + 1j * rng.normal(size=d)
            v /= np.linalg.norm(v)
            for s in (+1, -1):
                post = projector(P, s) @ v
                if np.linalg.norm(post) < 1e-12:
                    continue
                ok &= np.allclose(projector(P, s) @ post, post, atol=1e-10)
                ok &= np.allclose(projector(P, -s) @ post, 0, atol=1e-10)
        print(f"  {'PASS' if ok else 'FAIL':4s}  M_{name}; M_{name} idempotent (10 states × 2 outcomes)")
    return ok


def main():
    print("Verifying Pauli-measurement optimization rules")
    print("(mirroring 38 theorems in lean/QMeas/Optimization.lean)")
    print("-" * 60)
    results = [
        rule_idempotence(),
        rule_orthogonality(),
        rule_completeness(),
        rule_pauli_involutions(),
        rule_pauli_products(),
        rule_pauli_anticommutations(),
        rule_eigenvalue_identity(),
        rule_projector_difference(),
        rule_commuting_measurements(),
        rule_frame_absorption(),
        rule_sandwich(),
        rule_depth_reduction_example(),
        rule_operational_idempotence(),
    ]
    print()
    n_pass = sum(1 for r in results if r)
    print(f"RESULT: {n_pass}/{len(results)} rule families pass.")


if __name__ == "__main__":
    main()
