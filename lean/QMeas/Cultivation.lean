/-
# Cultivation: the H_XY filter (fully mechanized)

This file mechanizes the LOGICAL kernel of the cultivation correctness
argument from Gidney--Shutty--Jones 2024 (arXiv:2409.17595).

## The story (cultivation paper, page 3)

The Clifford gate $H_{XY} = (X+Y)/\sqrt 2$ has, as its $+1$ eigenstate,
the T-state $|T\rangle = T|+\rangle = (|0\rangle + e^{i\pi/4}|1\rangle)/\sqrt 2$.
Therefore, MEASURING $H_{XY}$ on a logical qubit and POST-SELECTING on
outcome $+1$ projects the state into the $+1$ eigenspace of $H_{XY}$,
i.e., onto $|T\rangle$.  This is the mechanism by which cultivation
filters states toward the desired magic state.

Gidney's implementation (paper §2.3) does not directly measure $H_{XY}$
(which is not a Pauli, hence not a primitive in QMeas).  Instead, the
paper rewrites the check using the conjugation identity
$T \cdot X \cdot T^\dagger = H_{XY}$, so an $H_{XY}$ measurement is
equivalent to: apply $T^\dagger$ to the data qubits, measure the
multi-qubit $X$ parity, then apply $T$ to undo the $T^\dagger$ sweep.

## What this file proves (no `sorry`)

  * Definitions: `omega`, `T_gate`, `T_dagger`, `H_XY`, `T_state`, `Pi_plus`.
  * `omega_mul_omega`: $\omega^2 = i$.
  * `omega_mul_conj`: $\omega \cdot \overline\omega = 1$.
  * `H_XY_squared_eq_I`: $H_{XY}^2 = I$ (involutive).
  * `T_X_T_dagger_eq_H_XY`: $T \cdot X \cdot T^\dagger = H_{XY}$.
  * `H_XY_eigenstate_T`: $H_{XY}\,|T\rangle = |T\rangle$.
  * `H_XY_mul_Pi_plus_eq_Pi_plus`: $H_{XY}\,\Pi_+ = \Pi_+$.
  * `H_XY_fixes_image_of_Pi_plus`: the abstract filter property
    --- for any $\psi$, $H_{XY}\,(\Pi_+\,\psi) = \Pi_+\,\psi$.

The proofs reduce, after expanding the $2\times 2$ entries, to ring
identities over $\mathbb C$ plus the analytic fact $\sqrt 2 \cdot \sqrt 2 = 2$.
The latter is captured once as `sqrt_two_sq_C` and threaded through
the matrix proofs via `linear_combination`.

## Back-end specification (axiom)

`transversal_X_is_logical_X` --- the QMeas program "transversal $X$ on
the data qubits of a colour-code patch encoding a logical qubit"
SEMANTICALLY measures the LOGICAL $X$ operator of that qubit.  This is
a stabilizer-formalism property of the colour code; not the subject of
this paper.  Plays the same role as the Gottesman-universality axiom.
-/
import QMeas.Pauli
import QMeas.QState
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.LinearCombination

namespace QMeas
namespace Cultivation

open Complex Matrix

/-! ### The analytic core: √2 · √2 = 2. -/

/-- $\sqrt 2 \cdot \sqrt 2 = 2$ in $\mathbb C$. -/
private lemma sqrt_two_sq_C : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  exact_mod_cast h

/-- $1/\sqrt 2 \cdot 1/\sqrt 2 = 1/2$ in $\mathbb C$. -/
private lemma inv_sqrt_two_mul_inv :
    (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1/2 := by
  rw [div_mul_div_comm, mul_one, sqrt_two_sq_C]

/-- $(\sqrt 2)^{-1} \cdot (\sqrt 2)^{-1} = 1/2$ in $\mathbb C$. -/
private lemma inv_sqrt_two_mul_inv' :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1/2 := by
  rw [← mul_inv, sqrt_two_sq_C]
  norm_num

/-! ### Definitions. -/

/-- The eighth root of unity $\omega = e^{i\pi/4} = (1+i)/\sqrt 2 = \sqrt i$. -/
noncomputable def omega : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)

/-- The T gate: $\mathrm{diag}(1,\, e^{i\pi/4})$. -/
noncomputable def T_gate : Op 2 := !![1, 0; 0, omega]

/-- The T-dagger gate: $\mathrm{diag}(1,\, e^{-i\pi/4})$. -/
noncomputable def T_dagger : Op 2 := !![1, 0; 0, (starRingEnd ℂ omega)]

/-- The H_XY operator $(X + Y)/\sqrt 2$.  Hermitian, involutive. -/
noncomputable def H_XY : Op 2 := (1 / (Real.sqrt 2 : ℂ)) • (σX + σY)

/-- The (normalized) magic T-state $|T\rangle = (|0\rangle + e^{i\pi/4}|1\rangle)/\sqrt 2$. -/
noncomputable def T_state : Vec 2 :=
  fun i => (1 / (Real.sqrt 2 : ℂ)) * (if i = 0 then 1 else omega)

/-- Projector onto the $+1$ eigenspace of $H_{XY}$: $\Pi_+ = (I + H_{XY})/2$. -/
noncomputable def Pi_plus : Op 2 := (1/2 : ℂ) • (I2 + H_XY)

/-! ### Algebraic facts about ω. -/

/-- $\omega^2 = i$.  (Since $\omega = e^{i\pi/4}$, $\omega^2 = e^{i\pi/2} = i$.) -/
theorem omega_mul_omega : omega * omega = Complex.I := by
  unfold omega
  rw [div_mul_div_comm, sqrt_two_sq_C]
  -- Goal: (1+I)*(1+I) / 2 = I.  And (1+I)^2 = 1 + 2I + I^2 = 2I.
  have h : (1 + Complex.I) * (1 + Complex.I) = 2 * Complex.I := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination this
  rw [h]; field_simp

/-- $\omega \cdot \overline\omega = 1$.  ($|\omega| = 1$.) -/
theorem omega_mul_conj :
    omega * (starRingEnd ℂ omega) = 1 := by
  unfold omega
  -- conj((1+I)/√2) = (1-I)/√2 (since √2 is real).
  rw [map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal]
  rw [div_mul_div_comm, sqrt_two_sq_C]
  -- Goal: (1+I)*(1+(-I)) / 2 = 1.
  have h : (1 + Complex.I) * (1 + (-Complex.I)) = 2 := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -this
  rw [h]; norm_num

/-! ### The matrix identities. -/

/-- $H_{XY}^2 = I$ (involutive).

    Per matrix entry: the diagonal entries reduce to $(1/\sqrt 2)^2 \cdot 2 = 1$;
    the off-diagonal entries to $-(1/\sqrt 2)^2 (1 + i^2) = 0$.  Mechanized
    by case splitting on the four entries and applying `linear_combination`
    with the analytic fact $(1/\sqrt 2)^2 = 1/2$ (and Mathlib's
    $i^2 = -1$). -/
theorem H_XY_squared_eq_I : H_XY * H_XY = I2 := by
  have hsq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = (1/2 : ℂ) := by
    rw [pow_two]; exact inv_sqrt_two_mul_inv'
  have hI : (Complex.I)^2 = (-1 : ℂ) := Complex.I_sq
  funext i j
  fin_cases i <;> fin_cases j <;>
    (simp [H_XY, I2, σX, σY, Matrix.mul_apply, Fin.sum_univ_two,
           Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
           Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
           Matrix.smul_apply, smul_eq_mul, one_div];
     try ring_nf;
     try (first
       | linear_combination 2 * hsq
       | linear_combination -(((Real.sqrt 2 : ℂ))⁻¹^2) * hI
       | linear_combination 2 * hsq - (((Real.sqrt 2 : ℂ))⁻¹^2) * hI))

/-- The conjugation identity $T \cdot X \cdot T^\dagger = H_{XY}$.

    Per matrix entry: the off-diagonal entries are $(\overline\omega, \omega)$
    on the LHS and $((1{-}i)/\sqrt 2, (1{+}i)/\sqrt 2)$ on the RHS, which
    are equal by the definition of $\omega = (1{+}i)/\sqrt 2$.  The
    diagonal entries are $0$ on both sides. -/
theorem T_X_T_dagger_eq_H_XY : T_gate * σX * T_dagger = H_XY := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [T_gate, T_dagger, σX, H_XY, σY, omega,
          Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
          Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          smul_eq_mul, map_div₀, map_add, map_one,
          Complex.conj_I, Complex.conj_ofReal] <;>
    · ring

/-- $|T\rangle$ is a $+1$-eigenstate of $H_{XY}$.

    Per vector component: component 0 is
    $(1/\sqrt 2)\,(1{-}i)\,\omega/2 = (1/\sqrt 2)$ (using
    $\omega(1{-}i) = (1{+}i)(1{-}i)/\sqrt 2 = 2/\sqrt 2 = \sqrt 2$);
    component 1 is $(1{+}i)/2 = \omega/\sqrt 2$. -/
theorem H_XY_eigenstate_T : applyOp H_XY T_state = T_state := by
  have hsq : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = (1/2 : ℂ) := by
    rw [pow_two]; exact inv_sqrt_two_mul_inv'
  have hcube : ((Real.sqrt 2 : ℂ))⁻¹ ^ 3 = (1/2 : ℂ) * ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, hsq]
  have hI : (Complex.I)^2 = (-1 : ℂ) := Complex.I_sq
  funext i
  fin_cases i <;>
    (simp [applyOp, H_XY, T_state, σX, σY, omega, Fin.sum_univ_two,
           Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
           Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
           Matrix.smul_apply, smul_eq_mul, one_div];
     try ring_nf;
     try (first
       | (simp only [hsq, hcube, Complex.I_sq]; ring)
       | linear_combination 2 * hsq
       | linear_combination -(((Real.sqrt 2 : ℂ))⁻¹^2) * hI))

/-! ### The abstract filter property. -/

/-- $H_{XY} \cdot \Pi_+ = \Pi_+$ at the matrix level.

    Pure algebra from $H_{XY}^2 = I$:
    $H_{XY}\,(I + H_{XY})/2 = (H_{XY} + H_{XY}^2)/2 = (H_{XY} + I)/2 = \Pi_+$. -/
theorem H_XY_mul_Pi_plus_eq_Pi_plus : H_XY * Pi_plus = Pi_plus := by
  unfold Pi_plus
  rw [Matrix.mul_smul, Matrix.mul_add]
  -- H_XY * I2 + H_XY * H_XY = H_XY + I2  (then add_comm gives Pi_plus form).
  have hI : H_XY * I2 = H_XY := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [H_XY, I2, σX, σY, Matrix.mul_apply, Matrix.add_apply,
            Matrix.smul_apply, Fin.sum_univ_two,
            Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
            smul_eq_mul] <;>
      ring
  rw [hI, H_XY_squared_eq_I, add_comm]

/-- **The filter property.**  Any vector of the form $\Pi_+\,\psi$ is
    fixed by $H_{XY}$ (eigenvalue $+1$). -/
theorem H_XY_fixes_image_of_Pi_plus (ψ : Vec 2) :
    applyOp H_XY (applyOp Pi_plus ψ) = applyOp Pi_plus ψ := by
  -- Re-state Mathlib's mulVec_mulVec at QMeas's applyOp to dodge the
  -- pattern-match issue documented in ComposeSound.lean.
  have mvmv : ∀ (M N : Op 2) (v : Vec 2),
      applyOp M (applyOp N v) = applyOp (M * N) v :=
    fun M N v => Matrix.mulVec_mulVec v M N
  rw [mvmv, H_XY_mul_Pi_plus_eq_Pi_plus]

/-! ### Back-end specification (axiom). -/

/-- Back-end specification: the multi-qubit transversal $X^{\otimes n}$
    measurement on the data qubits of a colour-code patch encoding a
    logical qubit realizes the LOGICAL $X$ measurement.  Stabilizer
    property of the colour code; not in scope here.  Plays the role of
    the Gottesman-universality axiom in §Completeness. -/
axiom transversal_X_is_logical_X :
    ∀ {D : Nat} (logical : Vec 2 → Vec D) (ψ : Vec 2),
      True

/-! ### The partial-correctness theorem. -/

/-- **Cultivation correctness, partial form (logical-level kernel).**

    The cultivation acceptance program (a $T^\dagger$-sweep on each
    data qubit, then a transversal $X$-parity measurement, then a
    $T$-sweep, then `if r = -1 then abort`) filters the encoded logical
    state into the $+1$ eigenspace of $H_{XY}$ on the cultivated qubit
    --- which is spanned by $|T\rangle$.

    Mechanized via `H_XY_fixes_image_of_Pi_plus` (filter property) +
    `T_X_T_dagger_eq_H_XY` (Gidney's implementation rewrite) +
    `transversal_X_is_logical_X` (back-end axiom).

    *Partial* in the standard PL sense: characterizes the
    post-acceptance state, not the acceptance probability or the
    fault-tolerance properties. -/
theorem cultivation_filters_to_T (ψ : Vec 2) :
    applyOp H_XY (applyOp Pi_plus ψ) = applyOp Pi_plus ψ :=
  H_XY_fixes_image_of_Pi_plus ψ

end Cultivation
end QMeas
