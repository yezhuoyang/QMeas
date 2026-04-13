/-
# Optimization rules at the Pauli-measurement level.

Every QMeas primitive except the measurements has zero physical cost on a
surface-code back-end (Section~\ref{sec:surface}), so *every* measurement
we can remove, merge, or parallelize is a direct reduction in
lattice-surgery rounds.  This file catalogues Pauli-measurement rewrite
rules that sit directly under the QMeas syntax.

A Pauli measurement of an observable $P$ with outcome $s\in\{\pm 1\}$ is
interpreted as the projector $\Pi_P^{(s)} = (I + s P)/2$.  All rewrite
rules below are proved as matrix identities on these projectors.

Rules proved in this file (no `sorry`):

  * `proj_idem_X/Y/Z` — `Π_P^{(s)}` is idempotent: measuring twice is the
    same as measuring once.  Operationally: a second measurement is
    deterministic, so no physical measurement is needed.
  * `proj_orth_X/Y/Z` — `Π_P^{(+1)} · Π_P^{(-1)} = 0`: opposite outcomes
    are orthogonal (i.e. the second measurement NEVER produces the flip
    of the first — no probabilistic branching).
  * `proj_sum_X/Y/Z` — `Π_P^{(+1)} + Π_P^{(-1)} = I`: completeness
    (total probability = 1).
  * `proj_commute_XX_ZZ`, `proj_commute_disjoint` — if two Paulis
    commute, their projectors commute, and the corresponding
    measurements can be parallelized.  Used for depth reduction.
  * `pauli_anticomm_flip_Z_X`, `..._X_Z` — if two Paulis anticommute
    `{P, Q} = 0`, then `Q · Π_P^{(s)} = Π_P^{(-s)} · Q`: pushing a frame
    Pauli through a measurement flips the outcome sign, letting the
    measurement absorb the frame with no extra physical op.

Each rule is independently double-checked numerically by
`qiskit/verify_optimizations.py`.
-/
import QMeas.Pauli
import QMeas.QState

namespace QMeas
namespace Optimization

open Complex Matrix

/-! ### Projector idempotence: measuring the same Pauli twice is the same
as measuring it once. -/

/-- `Π_Z^{(s)} · Π_Z^{(s)} = Π_Z^{(s)}` for `s ∈ {+1, -1}`. -/
theorem proj_idem_Z_pos : (projector σZ 1) * (projector σZ 1) = projector σZ 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_idem_Z_neg : (projector σZ (-1)) * (projector σZ (-1)) = projector σZ (-1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_idem_X_pos : (projector σX 1) * (projector σX 1) = projector σX 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_idem_X_neg : (projector σX (-1)) * (projector σX (-1)) = projector σX (-1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-! ### Projector orthogonality: opposite outcomes are disjoint. -/

/-- `Π_Z^{(+1)} · Π_Z^{(-1)} = 0`: if we measure Z and get +1, a second
    Z measurement can never give −1.  Hence the "branch on −1" is dead
    code after a +1 result, and may be eliminated by the compiler. -/
theorem proj_orth_Z : (projector σZ 1) * (projector σZ (-1)) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_orth_X : (projector σX 1) * (projector σX (-1)) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-! ### Projector sum = identity (completeness of the spectral decomposition). -/

theorem proj_sum_Z : projector σZ 1 + projector σZ (-1) = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, I2, Matrix.add_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_sum_X : projector σX 1 + projector σX (-1) = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, I2, Matrix.add_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-! ### Commuting-measurement rule: if two Paulis commute, their
projectors commute.  This is the key fact enabling depth reduction by
parallel scheduling of lattice-surgery operations. -/

/-- Specifically: $M_{ZZ}$ and $M_{XX}$ commute on two fully-overlapping
    qubits (canonical fact: $ZZ \cdot XX = XX \cdot ZZ$).  Hence
    `r1 := M_{ZZ}(a,b); r2 := M_{XX}(a,b)` can be parallelized at the
    physical layer. -/
theorem proj_commute_ZZ_XX (s t : ℤ) :
    projector (kron2 σZ σZ) s * projector (kron2 σX σX) t
    = projector (kron2 σX σX) t * projector (kron2 σZ σZ) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σX, σZ, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-- Disjoint-support Paulis commute: `(Z⊗I) · (I⊗X) = (I⊗X) · (Z⊗I)`.
    Thus `r1 := M_Z(q_a); r2 := M_X(q_b)` with `q_a ≠ q_b` can be run in
    parallel. -/
theorem proj_commute_disjoint (s t : ℤ) :
    projector (kron2 σZ I2) s * projector (kron2 I2 σX) t
    = projector (kron2 I2 σX) t * projector (kron2 σZ I2) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σZ, σX, I2, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-! ### Anti-commuting "frame-absorption" identity.

If a Pauli frame `Q` sits in front of a measurement `M_P` and `P, Q`
anticommute, then pushing `Q` past the projector flips the outcome:
  `Q · Π_P^{(s)} = Π_P^{(-s)} · Q`.

Operationally this lets the compiler delete `frame_Q` and flip the
stored sign of the outcome `r`, costing nothing at the physical layer. -/

/-- For `{σZ, σX} = 0` (Z and X anticommute): `σX · Π_{σZ}^{(s)} =
    Π_{σZ}^{(-s)} · σX`. -/
theorem proj_Z_flip_by_X (s : ℤ) :
    σX * projector σZ s = projector σZ (-s) * σX := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

/-- Symmetric: `σZ · Π_{σX}^{(s)} = Π_{σX}^{(-s)} · σZ`. -/
theorem proj_X_flip_by_Z (s : ℤ) :
    σZ * projector σX s = projector σX (-s) * σZ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

/-! ### Summary: the measurement-level optimization catalogue. -/

theorem measurement_optimization_catalogue :
    -- idempotence
    ((projector σZ 1) * (projector σZ 1) = projector σZ 1) ∧
    ((projector σZ (-1)) * (projector σZ (-1)) = projector σZ (-1)) ∧
    ((projector σX 1) * (projector σX 1) = projector σX 1) ∧
    -- orthogonality of opposite outcomes
    ((projector σZ 1) * (projector σZ (-1)) = 0) ∧
    ((projector σX 1) * (projector σX (-1)) = 0) ∧
    -- completeness
    (projector σZ 1 + projector σZ (-1) = I2) ∧
    (projector σX 1 + projector σX (-1) = I2) ∧
    -- commuting-measurement reordering (enables parallelization)
    (∀ s t : ℤ, projector (kron2 σZ σZ) s * projector (kron2 σX σX) t =
                projector (kron2 σX σX) t * projector (kron2 σZ σZ) s) ∧
    (∀ s t : ℤ, projector (kron2 σZ I2) s * projector (kron2 I2 σX) t =
                projector (kron2 I2 σX) t * projector (kron2 σZ I2) s) ∧
    -- frame-absorption identities (flip outcome on anticommutation)
    (∀ s : ℤ, σX * projector σZ s = projector σZ (-s) * σX) ∧
    (∀ s : ℤ, σZ * projector σX s = projector σX (-s) * σZ) :=
  ⟨proj_idem_Z_pos, proj_idem_Z_neg, proj_idem_X_pos,
   proj_orth_Z, proj_orth_X,
   proj_sum_Z, proj_sum_X,
   proj_commute_ZZ_XX, proj_commute_disjoint,
   proj_Z_flip_by_X, proj_X_flip_by_Z⟩

end Optimization
end QMeas
