/-
# CNOT gadget — formal correctness statement.

The QMeas one-ancilla CNOT gadget (canonical lattice-surgery CNOT) is:
```
ancilla a in |+>
r1 := M_{ZZ}(c, a)
r2 := M_{XX}(a, t)
r3 := M_Z(a)
if r2 == -1     : frame_Z(c)
if r1 ≠ r3      : frame_X(t)
discard a
```

For an arbitrary input `|ψ⟩ = a₀|00⟩ + a₁|01⟩ + a₂|10⟩ + a₃|11⟩` on `(c, t)`,
and the eight possible measurement outcomes `(r1, r2, r3) ∈ {±1}^3`, the
post-measurement state on `(c, t)`, after applying the byproduct Pauli encoded
in the frame, equals `CNOT|ψ⟩` (up to an unobservable global phase in the
two `(s1, -1, -s1)` branches).

The per-branch (unnormalized but rescaled) post-measurement states on `(c, t)`
were derived symbolically by `qiskit/derive_cnot_branches.py` and verified
numerically across many random inputs by `qiskit/verify_chosen_gadgets.py`.

Branch table (state on (c,t), correction, note):
```
(s1,s2,s3)  state_ct                  correction   result
(+,+,+)    ( a0,  a1,  a3,  a2)       I⊗I          = CNOT|ψ⟩
(+,+,-)    ( a1,  a0,  a2,  a3)       I⊗X          = CNOT|ψ⟩
(+,-,+)    ( a0,  a1, -a3, -a2)       Z⊗I          = CNOT|ψ⟩
(+,-,-)    (-a1, -a0,  a2,  a3)       Z⊗X          = -CNOT|ψ⟩  (global phase)
(-,+,+)    ( a1,  a0,  a2,  a3)       I⊗X          = CNOT|ψ⟩
(-,+,-)    ( a0,  a1,  a3,  a2)       I⊗I          = CNOT|ψ⟩
(-,-,+)    (-a1, -a0,  a2,  a3)       Z⊗X          = -CNOT|ψ⟩  (global phase)
(-,-,-)    ( a0,  a1, -a3, -a2)       Z⊗I          = CNOT|ψ⟩
```
-/
import QMeas.Pauli
import QMeas.QState
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

namespace QMeas
namespace Gadget.CNOT

open Complex

/-- The input state `|ψ⟩ = a₀|00⟩ + a₁|01⟩ + a₂|10⟩ + a₃|11⟩` on `(c, t)`. -/
def psi (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => a2
  | ⟨3, _⟩ => a3

/-- Branch (+,+,+) post-meas state on (c,t). -/
def state_ppp (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => a3
  | ⟨3, _⟩ => a2

/-- Branch (+,+,-) post-meas state. -/
def state_ppm (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => a1
  | ⟨1, _⟩ => a0
  | ⟨2, _⟩ => a2
  | ⟨3, _⟩ => a3

/-- Branch (+,-,+) post-meas state. -/
def state_pmp (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ =>  a0
  | ⟨1, _⟩ =>  a1
  | ⟨2, _⟩ => -a3
  | ⟨3, _⟩ => -a2

/-- Branch (+,-,-) post-meas state. -/
def state_pmm (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => -a1
  | ⟨1, _⟩ => -a0
  | ⟨2, _⟩ =>  a2
  | ⟨3, _⟩ =>  a3

/-- Branch (-,+,+) post-meas state. -/
def state_mpp (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => a1
  | ⟨1, _⟩ => a0
  | ⟨2, _⟩ => a2
  | ⟨3, _⟩ => a3

/-- Branch (-,+,-) post-meas state. -/
def state_mpm (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => a3
  | ⟨3, _⟩ => a2

/-- Branch (-,-,+) post-meas state. -/
def state_mmp (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ => -a1
  | ⟨1, _⟩ => -a0
  | ⟨2, _⟩ =>  a2
  | ⟨3, _⟩ =>  a3

/-- Branch (-,-,-) post-meas state. -/
def state_mmm (a0 a1 a2 a3 : ℂ) : Vec 4
  | ⟨0, _⟩ =>  a0
  | ⟨1, _⟩ =>  a1
  | ⟨2, _⟩ => -a3
  | ⟨3, _⟩ => -a2

/-- The bare action of the CNOT unitary on the input state. -/
theorem CNOT_apply (a0 a1 a2 a3 : ℂ) :
    CNOT *ᵥ psi a0 a1 a2 a3 = state_ppp a0 a1 a2 a3 := by
  funext i
  fin_cases i <;>
    simp [CNOT, psi, state_ppp, applyOp, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

/-! ### Macro to emit one branch lemma.

Each lemma states `correction *ᵥ state_branch a0 a1 a2 a3 = phase • CNOT *ᵥ ψ`
for a 4×4 correction matrix and a complex phase. -/

/-- Branch (+,+,+): no correction needed. -/
theorem branch_ppp_correct (a0 a1 a2 a3 : ℂ) :
    state_ppp a0 a1 a2 a3 = (CNOT *ᵥ psi a0 a1 a2 a3) := by
  exact (CNOT_apply a0 a1 a2 a3).symm

/-- Branch (+,+,-): apply `I⊗X`. -/
theorem branch_ppm_correct (a0 a1 a2 a3 : ℂ) :
    IX *ᵥ state_ppm a0 a1 a2 a3 = (CNOT *ᵥ psi a0 a1 a2 a3) := by
  funext i
  fin_cases i <;>
    simp [IX, kron2, CNOT, psi, state_ppm, I2, σX, applyOp,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.of_apply] <;>
    ring

/-- Branch (+,-,+): apply `Z⊗I`. -/
theorem branch_pmp_correct (a0 a1 a2 a3 : ℂ) :
    ZI *ᵥ state_pmp a0 a1 a2 a3 = (CNOT *ᵥ psi a0 a1 a2 a3) := by
  funext i
  fin_cases i <;>
    simp [ZI, kron2, CNOT, psi, state_pmp, I2, σZ, applyOp,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.of_apply] <;>
    ring

/-- Branch (+,-,-): apply `Z⊗X`; result equals `-CNOT|ψ⟩` (global phase). -/
theorem branch_pmm_correct (a0 a1 a2 a3 : ℂ) :
    ZX *ᵥ state_pmm a0 a1 a2 a3 = (-1 : ℂ) • ((CNOT *ᵥ psi a0 a1 a2 a3)) := by
  funext i
  fin_cases i <;>
    simp [ZX, kron2, CNOT, psi, state_pmm, σZ, σX, applyOp,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Branch (-,+,+): apply `I⊗X`. -/
theorem branch_mpp_correct (a0 a1 a2 a3 : ℂ) :
    IX *ᵥ state_mpp a0 a1 a2 a3 = (CNOT *ᵥ psi a0 a1 a2 a3) := by
  funext i
  fin_cases i <;>
    simp [IX, kron2, CNOT, psi, state_mpp, I2, σX, applyOp,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.of_apply] <;>
    ring

/-- Branch (-,+,-): no correction needed. -/
theorem branch_mpm_correct (a0 a1 a2 a3 : ℂ) :
    state_mpm a0 a1 a2 a3 = (CNOT *ᵥ psi a0 a1 a2 a3) := by
  exact (CNOT_apply a0 a1 a2 a3).symm

/-- Branch (-,-,+): apply `Z⊗X`; result equals `-CNOT|ψ⟩` (global phase). -/
theorem branch_mmp_correct (a0 a1 a2 a3 : ℂ) :
    ZX *ᵥ state_mmp a0 a1 a2 a3 = (-1 : ℂ) • ((CNOT *ᵥ psi a0 a1 a2 a3)) := by
  funext i
  fin_cases i <;>
    simp [ZX, kron2, CNOT, psi, state_mmp, σZ, σX, applyOp,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Branch (-,-,-): apply `Z⊗I`. -/
theorem branch_mmm_correct (a0 a1 a2 a3 : ℂ) :
    ZI *ᵥ state_mmm a0 a1 a2 a3 = (CNOT *ᵥ psi a0 a1 a2 a3) := by
  funext i
  fin_cases i <;>
    simp [ZI, kron2, CNOT, psi, state_mmm, I2, σZ, applyOp,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.of_apply] <;>
    ring

/-- Top-level QMeas CNOT-gadget correctness: every branch yields `CNOT|ψ⟩`
    (up to an unobservable global phase in two branches). -/
theorem CNOT_gadget_correct (a0 a1 a2 a3 : ℂ) :
    state_ppp a0 a1 a2 a3                = (CNOT *ᵥ psi a0 a1 a2 a3) ∧
    IX *ᵥ state_ppm a0 a1 a2 a3          = (CNOT *ᵥ psi a0 a1 a2 a3) ∧
    ZI *ᵥ state_pmp a0 a1 a2 a3          = (CNOT *ᵥ psi a0 a1 a2 a3) ∧
    ZX *ᵥ state_pmm a0 a1 a2 a3          = (-1 : ℂ) • ((CNOT *ᵥ psi a0 a1 a2 a3)) ∧
    IX *ᵥ state_mpp a0 a1 a2 a3          = (CNOT *ᵥ psi a0 a1 a2 a3) ∧
    state_mpm a0 a1 a2 a3                = (CNOT *ᵥ psi a0 a1 a2 a3) ∧
    ZX *ᵥ state_mmp a0 a1 a2 a3          = (-1 : ℂ) • ((CNOT *ᵥ psi a0 a1 a2 a3)) ∧
    ZI *ᵥ state_mmm a0 a1 a2 a3          = (CNOT *ᵥ psi a0 a1 a2 a3) :=
  ⟨branch_ppp_correct a0 a1 a2 a3,
   branch_ppm_correct a0 a1 a2 a3,
   branch_pmp_correct a0 a1 a2 a3,
   branch_pmm_correct a0 a1 a2 a3,
   branch_mpp_correct a0 a1 a2 a3,
   branch_mpm_correct a0 a1 a2 a3,
   branch_mmp_correct a0 a1 a2 a3,
   branch_mmm_correct a0 a1 a2 a3⟩

end Gadget.CNOT
end QMeas
