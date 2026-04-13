"""Derive the symbolic post-measurement state on (c,t) for each of the 8
branches of the CNOT gadget. Outputs Lean-friendly definitions."""

import sympy as sp
import numpy as np


def main():
    a0, a1, a2, a3 = sp.symbols("a0 a1 a2 a3")

    # Initial 8-dim state on (c, t, a). Indexing: idx = 4c + 2t + a.
    # |ψ⟩_{ct} ⊗ |+⟩_a, with |+⟩ = (|0⟩+|1⟩)/√2.
    inv_sqrt2 = sp.Rational(1) / sp.sqrt(2)
    coeffs = {
        (0, 0): a0, (0, 1): a1, (1, 0): a2, (1, 1): a3,
    }
    state = [0] * 8
    for (c, t), amp in coeffs.items():
        for a in (0, 1):
            idx = 4 * c + 2 * t + a
            state[idx] = amp * inv_sqrt2

    def project_zz_ca(v, s1):
        """Project on s1-eigenspace of Z⊗I⊗Z (Z on c, Z on a)."""
        out = [0] * 8
        for idx in range(8):
            c = (idx >> 2) & 1
            a = idx & 1
            ev = (-1) ** (c + a)  # eigenvalue of Z_c Z_a
            if ev == s1:
                out[idx] = v[idx]
        return out

    def project_xx_ta(v, s2):
        """Project on s2-eigenspace of I⊗X⊗X (X on t, X on a):
           P = (I + s2 * XX) / 2."""
        out = [0] * 8
        for idx in range(8):
            c = (idx >> 2) & 1
            t = (idx >> 1) & 1
            a = idx & 1
            flip = 4 * c + 2 * (1 - t) + (1 - a)
            out[idx] = (v[idx] + s2 * v[flip]) / 2
        return out

    def project_z_a(v, s3):
        """Project on s3-eigenspace of I⊗I⊗Z (Z on a)."""
        out = [0] * 8
        for idx in range(8):
            a = idx & 1
            ev = (-1) ** a
            if ev == s3:
                out[idx] = v[idx]
        return out

    def renormalize(v):
        """Symbolically renormalize assuming the input has a known squared norm
        of the form (|a0|²+|a1|²+|a2|²+|a3|²)*k for some rational k.  We use the
        constraint a0² + a1² + a2² + a3² = 1 (real-valued for symbolic clarity)
        to compute k and divide by sqrt(k)."""
        nsq = sum(sp.Abs(x) ** 2 for x in v)
        # Substitute the normalization constraint by computing nsq with
        # a0²+a1²+a2²+a3² = 1.  We only care about the rational scaling k.
        nsq_simplified = nsq.rewrite(sp.cos).subs({
            sp.Abs(a0)**2 + sp.Abs(a1)**2 + sp.Abs(a2)**2 + sp.Abs(a3)**2: 1
        })
        return [x for x in v]  # placeholder: keep unnormalized; we report shape

    print("# CNOT gadget per-branch (c,t)-state, unnormalized.")
    print("# Convention: idx = 2c + t for the 4-dim (c,t) basis.")
    print("# Branch (s1, s2, s3) ∈ {+1, -1}^3.")
    for s1 in (+1, -1):
        for s2 in (+1, -1):
            for s3 in (+1, -1):
                v = list(state)
                v = project_zz_ca(v, s1)
                v = project_xx_ta(v, s2)
                v = project_z_a(v, s3)
                # collect (c,t,a=fixed) components and report as (c,t) vector
                a_fixed = 0 if s3 == +1 else 1
                ct = []
                for c in (0, 1):
                    for t in (0, 1):
                        idx = 4 * c + 2 * t + a_fixed
                        ct.append(sp.simplify(v[idx]))
                # rescale by 2*sqrt(2) so the state is normalized when
                # |a0|^2+|a1|^2+|a2|^2+|a3|^2 = 1 (we divide each amp by inv_sqrt2/4
                # which is sqrt(2)/4 = 1/(2*sqrt(2)); inverse = 2*sqrt(2))
                rescale = 2 * sp.sqrt(2)
                ct_rescaled = [sp.simplify(x * rescale) for x in ct]
                print(f"\n# branch ({s1:+d},{s2:+d},{s3:+d})  a_fixed={a_fixed}")
                for k, val in zip(["00", "01", "10", "11"], ct_rescaled):
                    print(f"#   |{k}⟩_ct  : {val}")


if __name__ == "__main__":
    main()
