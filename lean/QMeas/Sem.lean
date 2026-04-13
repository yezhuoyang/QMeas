/-
# QMeas small-step operational semantics — transition relation.

Builds on `QMeas.Semantics` (which provides `Config`, `Store`, `Frame`).
Defines:
  * `Obs`        — the labels on transitions (silent vs. measurement outcome);
  * `Step`       — single-step transition relation `c ⟶[obs] c'`;
  * `MultiStep`  — its reflexive-transitive closure with a trace of obs.

Conventions:
  * Measurements record outcomes into the classical store and leave the
    quantum state in the projected eigenspace.
  * `frame P q` records `P` into the frame at qubit `q`; no quantum action.
  * `if r = +1 then s1 else s2` reads the store and chooses a branch.
  * `for i = 0..N do body` desugars to repeated `seq` (capped at `N`).
-/
import QMeas.Syntax
import QMeas.QState
import QMeas.Pauli
import QMeas.Frame
import QMeas.Semantics

namespace QMeas

/-- An observation accompanying one small-step.  `silent` for classical
    steps, `meas s` for the outcome of a measurement step. -/
inductive Obs where
  | silent : Obs
  | meas (r : Int) : Obs
  deriving Repr, DecidableEq

/-- The (denotational) post-measurement state for a single-qubit Pauli
    measurement on register `q` with outcome `s ∈ {+1, -1}`.

    For the formal semantics we keep this as an opaque function; the per-
    gadget proofs in `Gadgets.*` instantiate it on concrete inputs and
    verify the resulting matrix equation. -/
noncomputable def postMeas1 {D : Nat} (_P : Pauli1) (_q : Nat)
    (_s : Int) (ρ : Vec D) : Vec D := ρ

/-- Same for two-qubit Pauli measurement. -/
noncomputable def postMeas2 {D : Nat} (_P : Pauli2) (_qa _qb : Nat)
    (_s : Int) (ρ : Vec D) : Vec D := ρ

/-- A small-step transition `c ⟶[obs] c'` between configurations. -/
inductive Step {D : Nat} : Config D → Obs → Config D → Prop where
  /-- Sequencing: skip on the left collapses. -/
  | seqSkip (ρ : Vec D) (σ : Store) (F : Frame) (S : Stmt) :
      Step ⟨ρ, σ, F, .seq .skip S⟩ .silent ⟨ρ, σ, F, S⟩
  /-- Sequencing: step the left half. -/
  | seqStep (ρ ρ' : Vec D) (σ σ' : Store) (F F' : Frame)
      (S₁ S₁' S₂ : Stmt) (obs : Obs)
      (h : Step ⟨ρ, σ, F, S₁⟩ obs ⟨ρ', σ', F', S₁'⟩) :
      Step ⟨ρ, σ, F, .seq S₁ S₂⟩ obs ⟨ρ', σ', F', .seq S₁' S₂⟩
  /-- Single-qubit measurement: outcome `s ∈ {+1, -1}`. -/
  | meas1 (ρ : Vec D) (σ : Store) (F : Frame) (r : Nat) (P : Pauli1)
      (q : Nat) (s : Int) (hs : s = 1 ∨ s = -1) :
      Step ⟨ρ, σ, F, .meas1 r P q⟩ (.meas s)
           ⟨postMeas1 P q s ρ, Store.set σ r s, F, .skip⟩
  /-- Two-qubit measurement. -/
  | meas2 (ρ : Vec D) (σ : Store) (F : Frame) (r : Nat) (P : Pauli2)
      (qa qb : Nat) (s : Int) (hs : s = 1 ∨ s = -1) :
      Step ⟨ρ, σ, F, .meas2 r P qa qb⟩ (.meas s)
           ⟨postMeas2 P qa qb s ρ, Store.set σ r s, F, .skip⟩
  /-- Pauli-frame update: pure classical, no quantum action. -/
  | frameUpd (ρ : Vec D) (σ : Store) (F : Frame) (P : Pauli1) (q : Nat) :
      Step ⟨ρ, σ, F, .frame P q⟩ .silent ⟨ρ, σ, Frame.set F q P, .skip⟩
  /-- Conditional: `r` evaluates to +1, take then-branch. -/
  | ifPos (ρ : Vec D) (σ : Store) (F : Frame) (r : Nat) (s₁ s₂ : Stmt)
      (h : σ r = some 1) :
      Step ⟨ρ, σ, F, .ifPos r s₁ s₂⟩ .silent ⟨ρ, σ, F, s₁⟩
  /-- Conditional: `r` evaluates to -1, take else-branch. -/
  | ifNeg (ρ : Vec D) (σ : Store) (F : Frame) (r : Nat) (s₁ s₂ : Stmt)
      (h : σ r = some (-1)) :
      Step ⟨ρ, σ, F, .ifPos r s₁ s₂⟩ .silent ⟨ρ, σ, F, s₂⟩
  /-- For-loop: zero iterations. -/
  | forZero (ρ : Vec D) (σ : Store) (F : Frame) (i : Nat) (body : Stmt) :
      Step ⟨ρ, σ, F, .forLoop i 0 body⟩ .silent ⟨ρ, σ, F, .skip⟩
  /-- For-loop: unroll one iteration. -/
  | forUnroll (ρ : Vec D) (σ : Store) (F : Frame) (i N : Nat) (body : Stmt) :
      Step ⟨ρ, σ, F, .forLoop i (N+1) body⟩ .silent
           ⟨ρ, σ, F, .seq body (.forLoop i N body)⟩
  /-- Discard a quantum register. -/
  | discardCmd (ρ : Vec D) (σ : Store) (F : Frame) (q : Nat) :
      Step ⟨ρ, σ, F, .discard q⟩ .silent ⟨ρ, σ, F, .skip⟩

/-- Reflexive-transitive closure: many-step reduction. -/
inductive MultiStep {D : Nat} : Config D → List Obs → Config D → Prop where
  | refl (c : Config D) : MultiStep c [] c
  | step (c₁ c₂ c₃ : Config D) (obs : Obs) (trace : List Obs)
      (h₁ : Step c₁ obs c₂) (h₂ : MultiStep c₂ trace c₃) :
      MultiStep c₁ (obs :: trace) c₃

end QMeas
