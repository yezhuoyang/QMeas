/-
# Clifford → Pauli conjugation lift and its commutation lemma.

Reviewer comment R16 (in `.claude/notes/reviewer_plan.md`) asked for the
four handpicked matrix identities `H_commute_{X,Z}`, `S_commute_{X,Z}` to
be generalized into a function

    pushClifford : Cliff1 → Pauli1 → Pauli1

with a commutation lemma usable in the inductive proof of
`compose_sound` (R14).

Because the Clifford conjugation of `Y` picks up a sign

    H · Y · H = -Y        S · Y · S† = -X ,

we cannot state the commutation as a plain matrix equality if we want
the target to be a `Pauli1` (which carries no phase).  We therefore also
define

    pushSign : Cliff1 → Pauli1 → ℂ

returning `±1` (generalized to `ℂ` so that the structural-induction
product `pushSign c₂ ... * pushSign c₁ ...` type-checks), and state the
commutation with an explicit scalar:

    Cliff1.denote c * pauliMat P
        = pushSign c P • (pauliMat (pushClifford c P) * Cliff1.denote c).

This is strictly more informative than a "up to global phase" statement
and is exactly the shape the composition-soundness induction wants.
-/
import QMeas.Pauli
import QMeas.Clifford
import QMeas.Frame
import QMeas.Soundness         -- for H_commute_X, S_commute_Z

namespace QMeas
namespace CliffordPush

open Frame  -- for `pauliMat`

/-- Conjugation of a Pauli by a Clifford, ignoring the global phase.
    Extends `Frame.pushH` / `pushS` to whole circuits by structural
    recursion over `Cliff1`. -/
def pushClifford : Cliff1 → Pauli1 → Pauli1
  | .id,        p    => p
  | .H,         .X   => .Z
  | .H,         .Y   => .Y
  | .H,         .Z   => .X
  | .S,         .X   => .Y
  | .S,         .Y   => .X
  | .S,         .Z   => .Z
  | .seq c₁ c₂, p    => pushClifford c₂ (pushClifford c₁ p)

/-- The `±1` global phase incurred by conjugating `P` through `c`.
    Concretely: the only signed conjugations are `H · Y · H = -Y` and
    `S · Y · S† = -X`; every other single-gate Clifford-Pauli pair has
    sign `+1`.  Extended to `seq c₁ c₂` by multiplying the two inner
    signs (with the inner sign evaluated on `pushClifford c₁ P`). -/
noncomputable def pushSign : Cliff1 → Pauli1 → ℂ
  | .id,        _  => 1
  | .H,         .X => 1
  | .H,         .Y => -1
  | .H,         .Z => 1
  | .S,         .X => 1
  | .S,         .Y => -1
  | .S,         .Z => 1
  | .seq c₁ c₂, p  => pushSign c₂ (pushClifford c₁ p) * pushSign c₁ p

/-! ### The two missing matrix identities needed by the commutation proof. -/

/-- `H · σY = -σY · H`.  Used in the `.H / .Y` branch of the commutation
    theorem below. -/
theorem H_commute_Y :
    H_gate * σY = -(σY * H_gate) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [H_gate, σY, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.smul_apply, Matrix.neg_apply] <;>
    ring

/-- `S · σY = -σX · S`.  Used in the `.S / .Y` branch of the commutation
    theorem below. -/
theorem S_commute_Y :
    S_gate * σY = -(σX * S_gate) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [S_gate, σY, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.neg_apply] <;>
    ring

/-! ### Structural-induction commutation theorem. -/

/-- **Main theorem.**  For every single-qubit Clifford circuit `c` and
    every Pauli `P`,
        `denote c · pauliMat P  =  (pushSign c P) • (pauliMat (pushClifford c P) · denote c)`.

    Proof: induction on `c`.
    * `id`: both sides equal `pauliMat P` (using `one_mul` and `mul_one`).
    * `H`: case-split on `P` and apply `H_commute_X` / `H_commute_Y` /
      `H_commute_Z` from `Soundness.lean` (Y incurs the `-1`).
    * `S`: analogous with `S_commute_*`.
    * `seq c₁ c₂`: chain the inductive hypotheses using matrix
      associativity plus compatibility of scalar multiplication. -/
theorem pushClifford_commute :
    ∀ (c : Cliff1) (P : Pauli1),
      (Cliff1.denote c) * (Frame.pauliMat P) =
        (pushSign c P) • ((Frame.pauliMat (pushClifford c P)) * (Cliff1.denote c))
  | .id, P => by
      show I2 * Frame.pauliMat P = (1 : ℂ) • (Frame.pauliMat P * I2)
      funext i j
      cases P <;>
        fin_cases i <;> fin_cases j <;>
          simp [Frame.pauliMat, I2, σX, σY, σZ, Matrix.mul_apply, Fin.sum_univ_two,
                Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
                Matrix.smul_apply]
  | .H, .X => by
      simp only [Cliff1.denote, pushClifford, pushSign, Frame.pauliMat,
                 one_smul]
      exact QMeas.Soundness.H_commute_X
  | .H, .Z => by
      simp only [Cliff1.denote, pushClifford, pushSign, Frame.pauliMat,
                 one_smul]
      exact QMeas.Soundness.H_commute_Z
  | .H, .Y => by
      simp only [Cliff1.denote, pushClifford, pushSign, Frame.pauliMat]
      -- Goal: H_gate * σY = (-1) • (σY * H_gate)
      rw [H_commute_Y]
      simp [neg_smul, one_smul]
  | .S, .X => by
      simp only [Cliff1.denote, pushClifford, pushSign, Frame.pauliMat,
                 one_smul]
      exact QMeas.Soundness.S_commute_X
  | .S, .Z => by
      simp only [Cliff1.denote, pushClifford, pushSign, Frame.pauliMat,
                 one_smul]
      exact QMeas.Soundness.S_commute_Z
  | .S, .Y => by
      simp only [Cliff1.denote, pushClifford, pushSign, Frame.pauliMat]
      -- Goal: S_gate * σY = (-1) • (σX * S_gate)
      rw [S_commute_Y]
      simp [neg_smul, one_smul]
  | .seq c₁ c₂, P => by
      have h1 := pushClifford_commute c₁ P
      have h2 := pushClifford_commute c₂ (pushClifford c₁ P)
      show (Cliff1.denote c₂ * Cliff1.denote c₁) * Frame.pauliMat P =
           (pushSign c₂ (pushClifford c₁ P) * pushSign c₁ P) •
             (Frame.pauliMat (pushClifford c₂ (pushClifford c₁ P)) *
               (Cliff1.denote c₂ * Cliff1.denote c₁))
      calc (Cliff1.denote c₂ * Cliff1.denote c₁) * Frame.pauliMat P
          = Cliff1.denote c₂ * (Cliff1.denote c₁ * Frame.pauliMat P) := by
              rw [Matrix.mul_assoc]
        _ = Cliff1.denote c₂ *
              (pushSign c₁ P • (Frame.pauliMat (pushClifford c₁ P) * Cliff1.denote c₁)) := by
              rw [h1]
        _ = pushSign c₁ P •
              (Cliff1.denote c₂ * (Frame.pauliMat (pushClifford c₁ P) * Cliff1.denote c₁)) := by
              rw [Matrix.mul_smul]
        _ = pushSign c₁ P •
              ((Cliff1.denote c₂ * Frame.pauliMat (pushClifford c₁ P)) * Cliff1.denote c₁) := by
              rw [← Matrix.mul_assoc]
        _ = pushSign c₁ P •
              ((pushSign c₂ (pushClifford c₁ P) •
                (Frame.pauliMat (pushClifford c₂ (pushClifford c₁ P)) * Cliff1.denote c₂)) *
               Cliff1.denote c₁) := by
              rw [h2]
        _ = pushSign c₁ P •
              (pushSign c₂ (pushClifford c₁ P) •
                ((Frame.pauliMat (pushClifford c₂ (pushClifford c₁ P)) * Cliff1.denote c₂) *
                 Cliff1.denote c₁)) := by
              rw [Matrix.smul_mul]
        _ = (pushSign c₁ P * pushSign c₂ (pushClifford c₁ P)) •
              ((Frame.pauliMat (pushClifford c₂ (pushClifford c₁ P)) * Cliff1.denote c₂) *
               Cliff1.denote c₁) := by
              rw [smul_smul]
        _ = (pushSign c₂ (pushClifford c₁ P) * pushSign c₁ P) •
              ((Frame.pauliMat (pushClifford c₂ (pushClifford c₁ P)) * Cliff1.denote c₂) *
               Cliff1.denote c₁) := by
              rw [mul_comm]
        _ = (pushSign c₂ (pushClifford c₁ P) * pushSign c₁ P) •
              (Frame.pauliMat (pushClifford c₂ (pushClifford c₁ P)) *
                (Cliff1.denote c₂ * Cliff1.denote c₁)) := by
              rw [Matrix.mul_assoc]

end CliffordPush
end QMeas
