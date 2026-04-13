/-
# Single- and two-qubit Pauli operators as concrete complex matrices.

The QMeas measurement primitives are projective measurements of these Paulis.
We set up the matrices once here so the gadget proofs in `QMeas.Gadgets.*`
can do honest matrix computation.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace QMeas

open Complex Matrix

abbrev Op (n : Nat) := Matrix (Fin n) (Fin n) ℂ

/-- 2×2 identity. -/
def I2 : Op 2 := !![1, 0; 0, 1]

/-- Pauli X. -/
def σX : Op 2 := !![0, 1; 1, 0]

/-- Pauli Y. -/
def σY : Op 2 := !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z. -/
def σZ : Op 2 := !![1, 0; 0, -1]

/-- Hadamard gate. -/
noncomputable def H_gate : Op 2 := (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]

/-- Phase gate S = diag(1, i). -/
def S_gate : Op 2 := !![1, 0; 0, Complex.I]

/-- 4×4 identity (used for two-qubit operators). -/
def I4 : Op 4 := !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]

/-- Tensor (Kronecker) product of two 2×2 matrices, returning a 4×4 matrix.
    We use the convention that the *first* factor acts on the *left* qubit
    (qubit 0) and the *second* factor acts on the *right* qubit (qubit 1).
    Basis order: |00⟩, |01⟩, |10⟩, |11⟩. -/
def kron2 (A B : Op 2) : Op 4 :=
  Matrix.of fun (i j : Fin 4) =>
    let i0 : Fin 2 := ⟨i.val / 2, by omega⟩
    let i1 : Fin 2 := ⟨i.val % 2, by omega⟩
    let j0 : Fin 2 := ⟨j.val / 2, by omega⟩
    let j1 : Fin 2 := ⟨j.val % 2, by omega⟩
    A i0 j0 * B i1 j1

/-- Z⊗X as a 4×4 matrix. -/
def ZX : Op 4 := kron2 σZ σX

/-- Z⊗Z as a 4×4 matrix. -/
def ZZ : Op 4 := kron2 σZ σZ

/-- X⊗I as a 4×4 matrix (X on qubit 0). -/
def XI : Op 4 := kron2 σX I2

/-- I⊗X as a 4×4 matrix (X on qubit 1). -/
def IX : Op 4 := kron2 I2 σX

/-- Y⊗I as a 4×4 matrix (Y on qubit 0). -/
def YI : Op 4 := kron2 σY I2

/-- Z⊗I (Z on qubit 0). -/
def ZI : Op 4 := kron2 σZ I2

/-- I⊗Z (Z on qubit 1). -/
def IZ : Op 4 := kron2 I2 σZ

/-- CNOT with control on qubit 0, target on qubit 1.
    On basis: |00⟩↦|00⟩, |01⟩↦|01⟩, |10⟩↦|11⟩, |11⟩↦|10⟩. -/
def CNOT : Op 4 := !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]

end QMeas
