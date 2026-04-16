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

/-! ## Post-measurement state functions

Reviewer comment R08 in `notes/reviewer_plan.md` flagged that the previous
definitions of `postMeas1/2` were the identity function — silently making
the operational semantics' quantum action trivial.

The corrected definitions below are honest:

- For the canonical small-dimensional cases used by the gadget proofs
  (`D = 2` for a single-qubit measurement, `D = 4` for a two-qubit
  measurement on the same two qubits), we apply the s-eigenspace
  projector of the lifted Pauli operator directly via `applyOp`.
- For larger `D`, a Kronecker tensor lift of the small-dimensional
  projector to act on a specific qubit position is needed; that lift
  is not yet mechanized.  We return `ρ` unchanged in that case but
  clearly mark it as a placeholder, not a silent identity.

Renormalization (dividing by `√(⟨ρ|Π|ρ⟩)`) is the caller's
responsibility: `applyOp Π ρ` returns the unnormalized projection.
The gadget proofs in `Gadgets/*` work with the unnormalized form
because they reason about state ratios, not absolute amplitudes.
-/

/-- Apply the s-eigenspace projector of a single-qubit Pauli `P` to a
    1-qubit state.  This is the basis case of `postMeas1`. -/
noncomputable def postMeas1At1 (P : Pauli1) (s : Int) (ρ : Vec 2) : Vec 2 :=
  applyOp (projector (Frame.pauliMat P) s) ρ

/-- Apply the s-eigenspace projector of a two-qubit Pauli `P` to a
    2-qubit state.  This is the basis case of `postMeas2`. -/
noncomputable def postMeas2At2 (P : Pauli2) (s : Int) (ρ : Vec 4) : Vec 4 :=
  let mat : Op 4 := match P with
    | .XX => kron2 σX σX  | .ZZ => kron2 σZ σZ
    | .XZ => kron2 σX σZ  | .ZX => kron2 σZ σX
    | .YZ => kron2 σY σZ  | .ZY => kron2 σZ σY
    | .YX => kron2 σY σX  | .XY => kron2 σX σY
    | .YY => kron2 σY σY
  applyOp (projector mat s) ρ

/-- Post-measurement state for a single-qubit Pauli measurement on register
    `q` with outcome `s ∈ {+1, -1}`.  For `D = 2` (single-qubit system) this
    is the real projection; for `D > 2` we leave `ρ` unchanged as an
    explicit placeholder pending a Kronecker tensor lift. -/
noncomputable def postMeas1 {D : Nat} (P : Pauli1) (_q : Nat) (s : Int)
    (ρ : Vec D) : Vec D :=
  if h : D = 2 then by subst h; exact postMeas1At1 P s ρ
  else ρ

/-- Post-measurement state for a two-qubit Pauli measurement.  For `D = 4`
    (the two-qubit system that the measurement targets) this is the real
    projection; for `D > 4` we leave `ρ` unchanged as an explicit
    placeholder pending a Kronecker tensor lift. -/
noncomputable def postMeas2 {D : Nat} (P : Pauli2) (_qa _qb : Nat)
    (s : Int) (ρ : Vec D) : Vec D :=
  if h : D = 4 then by subst h; exact postMeas2At2 P s ρ
  else ρ

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
  /-- Conditional: `r` unset — reduce to `abort` rather than silently
      getting stuck.  This makes the ill-formed-program case observable
      in the accept/reject partition (reviewer R12 in
      `notes/reviewer_plan.md`).  A well-typed QMeas program binds
      every classical register it reads before the corresponding
      `ifPos`/`ifNeg` fires, so this rule is unreachable from
      well-typed inputs; it exists purely to rule out silent failure. -/
  | ifUnset (ρ : Vec D) (σ : Store) (F : Frame) (r : Nat) (s₁ s₂ : Stmt)
      (h : σ r = none) :
      Step ⟨ρ, σ, F, .ifPos r s₁ s₂⟩ .silent ⟨ρ, σ, F, .abort⟩
  /-- For-loop: zero iterations. -/
  | forZero (ρ : Vec D) (σ : Store) (F : Frame) (body : Stmt) :
      Step ⟨ρ, σ, F, .forLoop 0 body⟩ .silent ⟨ρ, σ, F, .skip⟩
  /-- For-loop: unroll one iteration. -/
  | forUnroll (ρ : Vec D) (σ : Store) (F : Frame) (N : Nat) (body : Stmt) :
      Step ⟨ρ, σ, F, .forLoop (N+1) body⟩ .silent
           ⟨ρ, σ, F, .seq body (.forLoop N body)⟩
  /-- Discard a quantum register.

      Reviewer comment R11 in `notes/reviewer_plan.md` flagged a real
      limitation here:  this rule does NOT physically remove qubit `q`
      from the quantum state `ρ`.  In a pure-state column-vector
      semantics (`Vec D := Fin D → ℂ`) there is no clean way to
      partial-trace a sub-system; the natural fix is either
       (a) move to density-matrix semantics
           (`ρ : Matrix (Fin D) (Fin D) ℂ`) and define `partialTrace`,
       (b) adopt a type-level linear discipline so that the syntax
           statically forbids referring to `q` after `discard q`,
           in the spirit of Qwire (R05).
      Both are substantive refactors and are tracked as future work.
      For now the rule is conservatively a no-op on `ρ` — soundness of
      compositions that touch a discarded qubit is therefore NOT
      established by the current operational semantics, and the
      reviewer paragraph in `theory.tex §Operational Semantics` is left
      in place as the audit-trail record of this limitation.
  -/
  | discardCmd (ρ : Vec D) (σ : Store) (F : Frame) (q : Nat) :
      Step ⟨ρ, σ, F, .discard q⟩ .silent ⟨ρ, σ, F, .skip⟩

/-- Reflexive-transitive closure: many-step reduction. -/
inductive MultiStep {D : Nat} : Config D → List Obs → Config D → Prop where
  | refl (c : Config D) : MultiStep c [] c
  | step (c₁ c₂ c₃ : Config D) (obs : Obs) (trace : List Obs)
      (h₁ : Step c₁ obs c₂) (h₂ : MultiStep c₂ trace c₃) :
      MultiStep c₁ (obs :: trace) c₃

end QMeas
