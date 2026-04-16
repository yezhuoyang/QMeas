/-
# QMeas probabilistic operational semantics (reviewer R09).

Extends the nondeterministic `Step` relation of `Sem.lean` with
Born-rule measurement weights.  The core idea: each nondeterministic
measurement branch is annotated with the probability
`p(s) = ‖Π_s ρ‖² / ‖ρ‖²` of obtaining outcome `s`.

This is an *additive* extension — the existing `Step` and `MultiStep`
are untouched.  Every existing proof continues to work.
-/
import QMeas.Sem

namespace QMeas

open Complex

/-! ## Squared norm of a state vector -/

noncomputable def normSq {D : Nat} (v : Vec D) : ℝ :=
  ∑ i : Fin D, (Complex.normSq (v i) : ℝ)

/-! ## Born-rule weight for a single measurement -/

/-- The Born-rule probability of obtaining outcome `s ∈ {+1, -1}` when
    measuring the Pauli operator `P` on state `ρ`:
    `p(s) = ‖Π_s ρ‖² / ‖ρ‖²`
    where `Π_s = (I + s P) / 2` is the s-eigenspace projector.
    Returns 0 when `‖ρ‖² = 0` (the zero state). -/
noncomputable def bornWeight {D : Nat} (P : Op D) (s : ℤ) (ρ : Vec D) : ℝ :=
  let projected := postMeas P s ρ
  if normSq ρ = 0 then 0
  else normSq projected / normSq ρ

/-! ## Probabilistic step relation

`PStep c (obs, w) c'` extends `Step c obs c'` by carrying a real-valued
weight `w`:
  * For silent steps, `w = 1` (no branching).
  * For measurement steps, `w = bornWeight P s ρ` (the Born-rule
    probability of the chosen outcome). -/

structure PStepResult (D : Nat) where
  obs    : Obs
  weight : ℝ
  config : Config D

/-- A probabilistic step: an underlying `Step` paired with its weight. -/
inductive PStep {D : Nat} : Config D → PStepResult D → Prop where
  | silent (c c' : Config D) (obs : Obs) (h : Step c obs c') (ho : obs = .silent) :
      PStep c ⟨obs, 1, c'⟩
  | meas1_weighted (ρ : Vec D) (σ : Store) (F : Frame)
      (r : Nat) (P : Pauli1) (q : Nat) (s : Int) (hs : s = 1 ∨ s = -1)
      (mat : Op D) (w : ℝ) (hw : w = bornWeight mat s ρ) :
      PStep ⟨ρ, σ, F, .meas1 r P q⟩
            ⟨.meas s, w, ⟨postMeas1 P q s ρ, Store.set σ r s, F, .skip⟩⟩
  | meas2_weighted (ρ : Vec D) (σ : Store) (F : Frame)
      (r : Nat) (P : List Pauli1) (qa qb : Nat) (s : Int)
      (hs : s = 1 ∨ s = -1)
      (mat : Op D) (w : ℝ) (hw : w = bornWeight mat s ρ) :
      PStep ⟨ρ, σ, F, .meas2 r P qa qb⟩
            ⟨.meas s, w, ⟨postMeas2 P qa qb s ρ, Store.set σ r s, F, .skip⟩⟩

/-! ## Multi-step trace with cumulative probability -/

/-- A probabilistic multi-step reduction: a sequence of `PStep`s,
    carrying the product of all branch weights.  The cumulative
    weight `∏ w_i` is the probability of the full trace. -/
inductive PMultiStep {D : Nat} : Config D → List Obs → ℝ → Config D → Prop where
  | refl (c : Config D) : PMultiStep c [] 1 c
  | step (c₁ c₂ c₃ : Config D) (obs : Obs) (w : ℝ)
      (trace : List Obs) (cumWeight : ℝ)
      (h₁ : PStep c₁ ⟨obs, w, c₂⟩)
      (h₂ : PMultiStep c₂ trace cumWeight c₃) :
      PMultiStep c₁ (obs :: trace) (w * cumWeight) c₃

/-! ## Key property: Born-rule weights sum to 1

For a single measurement with Pauli projector `P` (satisfying `P² = I`),
the weights of the two branches sum to 1:
  `bornWeight P 1 ρ + bornWeight P (-1) ρ = 1`
provided `‖ρ‖² ≠ 0`. -/

theorem bornWeight_sum_one {D : Nat} (P : Op D) (ρ : Vec D)
    (hP : ∀ i j, (∑ k, P i k * P k j) = if i = j then 1 else 0)
    (hρ : normSq ρ ≠ 0) :
    bornWeight P 1 ρ + bornWeight P (-1) ρ = 1 := by
  sorry

end QMeas
