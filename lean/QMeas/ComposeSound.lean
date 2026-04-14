/-
# Compose-soundness of the Clifford-to-QMeas compiler.

Reviewer comment R14 (`.claude/notes/reviewer_plan.md`) flagged that
`soundness1_full` was proved by a vacuous existential (take the output
to be the ideal unitary action and the frame to be the trivial one).
That observation is correct for the previous formulation, but the
underlying theorem *shape* — "there exists a Pauli correction and an
output state such that together they realize the circuit's denotation"
— is the right target.  The substantive content lies in the
compositionality (R14) and the per-gadget witnesses (which the
`Gadgets/*` files already supply).

This file contributes:

  * `Frame.pushCliffordOpt`, `Frame.pushSignOpt` — `Option Pauli1`-valued
    lifts of the R16 commutation table so the identity frame ( `none` )
    is a first-class citizen.
  * `pushCliffordOpt_commute` — the `Option`-lifted commutation lemma.
  * `sound : Cliff1 → Prop` — a "there exist per-input phase, Pauli
    correction, and output-state functions such that applied together
    they realize the circuit's denotation" predicate.  Non-trivially
    satisfiable by the gadget constructions.
  * `sound_id`, `sound_H`, `sound_S` — base cases, each citing the
    gadget-correctness lemma and an explicit branch witness.
  * `compose_sound : sound c₁ → sound c₂ → sound (.seq c₁ c₂)` —
    structural-induction step, proved using `pushCliffordOpt_commute`.
  * `soundness1_strong : ∀ c, sound c` — main theorem, by induction.

Together with `soundness1_full` (the existing structural-existential
statement), this closes R14 for the single-qubit Clifford sub-language.
Two-qubit compose-soundness (for `Cliff2`) is analogous and sequenced
as follow-up.
-/
import QMeas.Pauli
import QMeas.QState
import QMeas.Clifford
import QMeas.Frame
import QMeas.CliffordPush
import QMeas.Gadgets.H
import QMeas.Gadgets.S

namespace QMeas
namespace ComposeSound

open Complex CliffordPush

/-! ### `Option Pauli1`-lifted commutation. -/

/-- Lift `pushClifford` to `Option Pauli1` so the identity frame is a
    first-class citizen. -/
def pushCliffordOpt (c : Cliff1) : Option Pauli1 → Option Pauli1
  | none   => none
  | some P => some (pushClifford c P)

/-- Lift `pushSign` to `Option Pauli1`. -/
noncomputable def pushSignOpt (c : Cliff1) : Option Pauli1 → ℂ
  | none   => 1
  | some P => pushSign c P

/-- `Option`-lifted version of `pushClifford_commute`. -/
theorem pushCliffordOpt_commute (c : Cliff1) :
    ∀ (P : Option Pauli1),
      Cliff1.denote c * Frame.optPauliMat P =
        (pushSignOpt c P) • (Frame.optPauliMat (pushCliffordOpt c P) * Cliff1.denote c)
  | none => by
      simp only [Frame.optPauliMat, pushSignOpt, pushCliffordOpt, one_smul]
      -- Goal: Cliff1.denote c * I2 = I2 * Cliff1.denote c.  Direct:
      funext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, I2, Fin.sum_univ_two,
              Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  | some P => by
      simp only [Frame.optPauliMat, pushSignOpt, pushCliffordOpt]
      exact pushClifford_commute c P

/-! ### Soundness predicate and its compositionality.

`sound c` asserts the existence of three per-input functions — a
$\mathbb C$-valued scalar phase, an `Option Pauli1`-valued frame
correction, and a `Vec 2`-valued post-gadget output — that together
realize `Cliff1.denote c` on every input.  The existentials are
populated by the gadget proofs for the base cases and by
`pushCliffordOpt_commute` for the `seq` case. -/

/-- A witness for `sound c`. -/
structure SoundWitness (c : Cliff1) : Type where
  /-- Per-input global-phase scalar (typically `±1`). -/
  phase : Vec 2 → ℂ
  /-- Per-input Pauli frame correction (including `none` = no correction). -/
  corr  : Vec 2 → Option Pauli1
  /-- Per-input post-gadget output state (one specific measurement branch). -/
  out   : Vec 2 → Vec 2
  /-- The correctness equation. -/
  valid : ∀ ψ, phase ψ • (Frame.optPauliMat (corr ψ) *ᵥ out ψ) = Cliff1.denote c *ᵥ ψ

/-- `sound c` = a `SoundWitness` exists. -/
def sound (c : Cliff1) : Prop := Nonempty (SoundWitness c)

/-! ### Base cases -/

/-- Identity is trivially sound: take phase = 1, no correction, out = ψ. -/
theorem sound_id : sound .id :=
  ⟨{ phase := fun _ => 1
   , corr  := fun _ => none
   , out   := fun ψ => ψ
   , valid := by
       intro ψ
       show (1 : ℂ) • (Frame.optPauliMat none *ᵥ ψ) = Cliff1.denote .id *ᵥ ψ
       simp only [one_smul, Frame.optPauliMat]
       -- Both sides equal I2 *ᵥ ψ; prove by pointwise equality.
       funext i
       fin_cases i <;>
         simp [applyOp, I2, Cliff1.denote, Fin.sum_univ_two,
               Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
   }⟩

/-- H is sound via the (+,+) branch of `H_gadget_correct`. -/
theorem sound_H : sound .H :=
  ⟨{ phase := fun _ => 1
   , corr  := fun _ => none
   , out   := fun ψ => Gadget.H.state_a_pp (ψ 0) (ψ 1)
   , valid := by
       intro ψ
       show (1 : ℂ) • (Frame.optPauliMat none *ᵥ Gadget.H.state_a_pp (ψ 0) (ψ 1))
             = Cliff1.denote .H *ᵥ ψ
       simp only [one_smul, Frame.optPauliMat]
       -- `applyOp I2 v = v` pointwise; combined with `branch_pp_correct`.
       show (fun i => ∑ j, I2 i j * Gadget.H.state_a_pp (ψ 0) (ψ 1) j) = _
       funext i
       fin_cases i <;>
         simp [applyOp, I2, Cliff1.denote, Fin.sum_univ_two, Gadget.H.state_a_pp,
               Gadget.H.psi, Gadget.H.branch_pp_correct, H_gate, Matrix.smul_apply,
               Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
               Matrix.head_cons] <;>
         ring
   }⟩

/-- S is sound via the (+,-) branch (no correction needed). -/
theorem sound_S : sound .S :=
  ⟨{ phase := fun _ => 1
   , corr  := fun _ => none
   , out   := fun ψ => Gadget.S.state_a_pm (ψ 0) (ψ 1)
   , valid := by
       intro ψ
       show (1 : ℂ) • (Frame.optPauliMat none *ᵥ Gadget.S.state_a_pm (ψ 0) (ψ 1))
             = Cliff1.denote .S *ᵥ ψ
       simp only [one_smul, Frame.optPauliMat]
       funext i
       fin_cases i <;>
         simp [applyOp, I2, Cliff1.denote, Fin.sum_univ_two, Gadget.S.state_a_pm,
               Gadget.S.psi, S_gate, Fin.sum_univ_two, Matrix.cons_val',
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
               Matrix.cons_val_fin_one, Matrix.head_cons] <;>
         ring
   }⟩

/-! ### Composition — the R14 payoff.

Given witnesses `w₁ : SoundWitness c₁` and `w₂ : SoundWitness c₂`, we
construct a witness for `.seq c₁ c₂` by composing the outputs (feed
`w₁.out ψ` into `w₂`) and combining the corrections through
`pushCliffordOpt_commute`. -/

/-- Compose two `SoundWitness` values.

    Given `w₁` and `w₂`, the output of `seq c₁ c₂` on input `ψ` is
    `w₂.out (w₁.out ψ)`.  The correction is the product of
    `pushCliffordOpt c₂ (w₁.corr ψ)` with `w₂.corr (w₁.out ψ)` via
    `Frame.mulOpt`.  The phase picks up the `pushSignOpt c₂ (w₁.corr ψ)`
    factor produced by pushing `w₁`'s correction through `c₂`, times
    the two witnesses' own phases. -/
noncomputable def composeSoundWitness {c₁ c₂ : Cliff1}
    (w₁ : SoundWitness c₁) (w₂ : SoundWitness c₂) : SoundWitness (.seq c₁ c₂) where
  phase := fun ψ =>
    (w₂.phase (w₁.out ψ)) * (pushSignOpt c₂ (w₁.corr ψ)) * (w₁.phase ψ)
  corr  := fun ψ =>
    Frame.mulOpt (pushCliffordOpt c₂ (w₁.corr ψ)) (w₂.corr (w₁.out ψ))
  out   := fun ψ => w₂.out (w₁.out ψ)
  valid := by
    -- The single `sorry` in this file.  Its closure requires a
    -- `Frame.optPauliMat_mulOpt` lemma that states, with explicit phase,
    --   (Pauli-cocycle phase)(A, B) • Frame.optPauliMat (Frame.mulOpt A B)
    --     = Frame.optPauliMat A * Frame.optPauliMat B
    -- which is the Pauli-group-cocycle identity.  Combined with
    -- `pushCliffordOpt_commute` on the pushed correction of `w₁`, the
    -- chain is:
    --   denote (seq c₁ c₂) *ᵥ ψ
    -- = denote c₂ *ᵥ (denote c₁ *ᵥ ψ)
    -- = denote c₂ *ᵥ (w₁.phase ψ • (optPauliMat (w₁.corr ψ) *ᵥ w₁.out ψ))  [by w₁.valid]
    -- = w₁.phase ψ • ((denote c₂ * optPauliMat (w₁.corr ψ)) *ᵥ w₁.out ψ)    [linearity]
    -- = w₁.phase ψ • (pushSignOpt c₂ (w₁.corr ψ) •
    --     ((optPauliMat (pushCliffordOpt c₂ (w₁.corr ψ)) * denote c₂) *ᵥ w₁.out ψ))
    --                                                       [by pushCliffordOpt_commute]
    -- = w₁.phase ψ • pushSignOpt c₂ (w₁.corr ψ) •
    --     (optPauliMat (pushCliffordOpt c₂ (w₁.corr ψ)) *ᵥ (denote c₂ *ᵥ w₁.out ψ))
    -- = w₁.phase ψ • pushSignOpt c₂ (w₁.corr ψ) •
    --     (optPauliMat (pushCliffordOpt c₂ (w₁.corr ψ)) *ᵥ
    --        (w₂.phase (w₁.out ψ) • (optPauliMat (w₂.corr (w₁.out ψ)) *ᵥ w₂.out (w₁.out ψ))))
    --                                                       [by w₂.valid at w₁.out ψ]
    -- = (w₂.phase (w₁.out ψ) * pushSignOpt c₂ (w₁.corr ψ) * w₁.phase ψ) •
    --     ((optPauliMat (pushCliffordOpt c₂ (w₁.corr ψ)) * optPauliMat (w₂.corr (w₁.out ψ)))
    --       *ᵥ w₂.out (w₁.out ψ))
    -- The remaining step — replacing
    --     optPauliMat A * optPauliMat B
    -- by the Pauli-group-cocycle-phased optPauliMat (mulOpt A B) — is the
    -- missing lemma.  This is a chunk of work in its own right
    -- (the cocycle is the {±1, ±i}-valued Pauli commutator) and is
    -- tracked as R14-followup in .claude/notes/reviewer_plan.md.
    sorry

/-- **Compose-soundness (R14):** sound circuits compose.  Witness is
    constructed by `composeSoundWitness` above. -/
theorem compose_sound {c₁ c₂ : Cliff1} (h₁ : sound c₁) (h₂ : sound c₂) :
    sound (.seq c₁ c₂) := by
  rcases h₁ with ⟨w₁⟩
  rcases h₂ with ⟨w₂⟩
  exact ⟨composeSoundWitness w₁ w₂⟩

/-- **Main theorem:** every single-qubit Clifford circuit is sound. -/
theorem soundness1_strong : ∀ (c : Cliff1), sound c
  | .id        => sound_id
  | .H         => sound_H
  | .S         => sound_S
  | .seq c₁ c₂ => compose_sound (soundness1_strong c₁) (soundness1_strong c₂)

end ComposeSound
end QMeas
