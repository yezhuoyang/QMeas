/-
# Quantum states as column vectors and projective measurements.

For the gadget proofs we represent quantum states of `n`-qubit systems as
functions `Fin (2^n) → ℂ` (equivalently, column vectors).  We define the
projector onto the ±1 eigenspace of a Hermitian Pauli operator with
eigenvalues ±1, and the post-measurement state.
-/
import QMeas.Pauli
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

namespace QMeas

open Matrix

/-- Pure state of an `n`-dim Hilbert space (a column vector). -/
abbrev Vec (n : Nat) := Fin n → ℂ

/-- Action of a matrix on a vector. -/
noncomputable def applyOp {n : Nat} (M : Op n) (v : Vec n) : Vec n :=
  fun i => ∑ j, M i j * v j

@[inherit_doc] infixr:75 " *ᵥ " => applyOp

/-- The projector onto the `s`-eigenspace of `P` (eigenvalue `s ∈ {+1, -1}`):
    `(I + s • P) / 2`.  We pass `s : ℤ` (intended values ±1). -/
noncomputable def projector {n : Nat} (P : Op n) (s : ℤ) : Op n :=
  fun i j => ((if i = j then (1 : ℂ) else 0) + (s : ℂ) * P i j) / 2

/-- The post-measurement (unnormalized) state, given outcome `s ∈ {+1, -1}`. -/
noncomputable def postMeas {n : Nat} (P : Op n) (s : ℤ) (v : Vec n) : Vec n :=
  applyOp (projector P s) v

end QMeas
