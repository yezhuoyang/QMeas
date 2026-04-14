/-
# QMeas configurations and small-step operational semantics.

A configuration is a 4-tuple `⟨ρ, σ, F, S⟩` of:
  * `ρ`     : the quantum state of the live qubits (here a vector for purity);
  * `σ`     : the classical store mapping bit names to ±1 outcomes;
  * `F`     : the Pauli frame (a per-qubit single-qubit Pauli operator);
  * `S`     : the QMeas statement to execute next.

We give a *deterministic-branch* semantics: each measurement step is indexed
by the outcome `s ∈ {+1, -1}`; the actual probabilistic semantics is recovered
by summing over the two branches weighted by the squared norm of the
post-measurement state.
-/
import QMeas.Syntax
import QMeas.QState
import QMeas.Frame

namespace QMeas

/-- Classical store: a partial map from bit-name (Nat) to ±1. -/
abbrev Store := Nat → Option Int

/-- Pauli frame: per-qubit single-qubit Pauli (default `X`/`Y`/`Z`/`I` —
    we encode as `Option Pauli1` with `none` meaning identity). -/
abbrev Frame := Nat → Option Pauli1

/-- A QMeas configuration parameterized by the global Hilbert-space dimension
    `D = 2^n` for `n` live qubits. -/
structure Config (D : Nat) where
  state : Vec D
  store : Store
  frame : Frame
  prog  : Stmt

/-- Update a store at a single key. -/
def Store.set (σ : Store) (k : Nat) (v : Int) : Store :=
  fun k' => if k' = k then some v else σ k'

/-- Compose a Pauli into the frame at a single key.
    Previously this was an overwrite; the corrected behaviour multiplies
    the existing frame by `P` using `Frame.mulOpt` from `QMeas.Frame`,
    so two successive `frame_X(q); frame_Z(q)` correctly compose to `Y`
    (in the projective Pauli group), not to `Z`.
    Reviewer comment R10 in `notes/reviewer_plan.md`. -/
def Frame.set (F : Frame) (k : Nat) (P : Pauli1) : Frame :=
  fun k' => if k' = k then Frame.mulOpt (F k') (some P) else F k'

/-- Empty store. -/
def Store.empty : Store := fun _ => none

/-- Empty frame. -/
def Frame.empty : Frame := fun _ => none

/-! ### Operational semantics — definitional sketch.

For now we record the shape of the small-step rules; the gadget proofs in
`QMeas.Gadgets.*` work directly at the matrix level (a denotational view).
A full mechanized small-step semantics is future work and lives here. -/

end QMeas
