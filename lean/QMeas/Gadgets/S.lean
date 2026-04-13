/-
# Phase gate gadget — formal correctness statement.

The QMeas S-gadget is:
```
ancilla a in |+>
r1 := M_{ZZ}(q, a)
r2 := M_Y(q)
if (correction table) : frame_X / frame_Y / frame_Z (a)
discard q
```

For an arbitrary input `|ψ⟩ = α|0⟩ + β|1⟩` on `q` and the four possible
measurement outcomes `(r1, r2) ∈ {±1}^2`, the post-measurement state on `a`,
after applying the byproduct Pauli encoded in the frame, equals `S|ψ⟩` (up
to an unobservable global phase in the `(-1, +1)` branch).

  branch (+1, +1)  →  Z correction       (state_a = α|0⟩ - iβ|1⟩)
  branch (+1, -1)  →  I correction       (state_a = α|0⟩ + iβ|1⟩ = S|ψ⟩)
  branch (-1, +1)  →  Y correction       (state_a = -iβ|0⟩ + α|1⟩ ; Y·state_a = -i·S|ψ⟩)
  branch (-1, -1)  →  X correction       (state_a = iβ|0⟩ + α|1⟩)

These post-measurement states were derived by direct application of the
projectors `(I ± ZZ)/2` then `(I ± Y⊗I)/2` to the input
`|ψ⟩ ⊗ |+⟩` and renormalizing.  They are independently double-checked by
`qiskit/verify_chosen_gadgets.py`.
-/
import QMeas.Pauli
import QMeas.QState
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

namespace QMeas
namespace Gadget.S

open Complex

/-- The input qubit state `α|0⟩ + β|1⟩` viewed as an element of `Vec 2`. -/
def psi (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => α
  | ⟨1, _⟩ => β

/-- After both measurements `(r1=+1, r2=+1)`, the state on `a` is
    `α|0⟩ - iβ|1⟩`. -/
def state_a_pp (α β : ℂ) : Vec 2
  | ⟨0, _⟩ =>  α
  | ⟨1, _⟩ => -Complex.I * β

/-- After both measurements `(r1=+1, r2=-1)`, the state on `a` is `S|ψ⟩`. -/
def state_a_pm (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => α
  | ⟨1, _⟩ => Complex.I * β

/-- After both measurements `(r1=-1, r2=+1)`, the state on `a` is
    `-iβ|0⟩ + α|1⟩`. -/
def state_a_mp (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => -Complex.I * β
  | ⟨1, _⟩ => α

/-- After both measurements `(r1=-1, r2=-1)`, the state on `a` is
    `iβ|0⟩ + α|1⟩`. -/
def state_a_mm (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => Complex.I * β
  | ⟨1, _⟩ => α

/-- The phase gate applied to `|ψ⟩ = α|0⟩ + β|1⟩` is `α|0⟩ + iβ|1⟩`. -/
theorem S_apply (α β : ℂ) :
    S_gate *ᵥ psi α β = state_a_pm α β := by
  funext i
  fin_cases i <;>
    simp [S_gate, psi, state_a_pm, applyOp, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-- Branch (+1, +1): applying `Z` to the post-measurement state on `a`
    yields `S|ψ⟩`. -/
theorem branch_pp_correct (α β : ℂ) :
    σZ *ᵥ state_a_pp α β = (S_gate *ᵥ psi α β) := by
  funext i
  fin_cases i <;>
    simp [σZ, S_gate, psi, state_a_pp, applyOp, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-- Branch (+1, -1): no correction needed; state on `a` already equals
    `S|ψ⟩`. -/
theorem branch_pm_correct (α β : ℂ) :
    state_a_pm α β = (S_gate *ᵥ psi α β) :=
  (S_apply α β).symm

/-- Branch (-1, +1): applying `Y` to the post-measurement state on `a`
    yields `S|ψ⟩` up to the unobservable global phase `-i`. -/
theorem branch_mp_correct (α β : ℂ) :
    σY *ᵥ state_a_mp α β = (-Complex.I) • ((S_gate *ᵥ psi α β)) := by
  funext i
  fin_cases i <;>
    simp [σY, S_gate, psi, state_a_mp, applyOp, Matrix.smul_apply,
          Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Branch (-1, -1): applying `X` to the post-measurement state on `a`
    yields `S|ψ⟩`. -/
theorem branch_mm_correct (α β : ℂ) :
    σX *ᵥ state_a_mm α β = (S_gate *ᵥ psi α β) := by
  funext i
  fin_cases i <;>
    simp [σX, S_gate, psi, state_a_mm, applyOp, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-- Top-level QMeas S-gadget correctness. -/
theorem S_gadget_correct (α β : ℂ) :
    σZ *ᵥ state_a_pp α β = (S_gate *ᵥ psi α β) ∧
    state_a_pm α β       = (S_gate *ᵥ psi α β) ∧
    σY *ᵥ state_a_mp α β = (-Complex.I) • ((S_gate *ᵥ psi α β)) ∧
    σX *ᵥ state_a_mm α β = (S_gate *ᵥ psi α β) :=
  ⟨branch_pp_correct α β,
   branch_pm_correct α β,
   branch_mp_correct α β,
   branch_mm_correct α β⟩

end Gadget.S
end QMeas
