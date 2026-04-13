/-
# Hadamard gadget — formal correctness statement.

The QMeas H-gadget is:
```
ancilla a in |0>
r1 := M_{ZX}(q, a)        -- Z on q, X on a
r2 := M_X(q)
if r2 == -1 : frame_X(a)
if r1 == -1 : frame_Z(a)
discard q
```

For an arbitrary input `|ψ⟩ = α|0⟩ + β|1⟩` on `q` and the four possible
measurement outcomes `(r1, r2) ∈ {±1}^2`, the post-measurement state on `a`,
after applying the byproduct Pauli encoded in the frame, equals `H |ψ⟩`.

We split into four `branch_*` lemmas, one per outcome:

  branch (+1, +1)  →  no correction (frame holds I)
  branch (+1, -1)  →  X correction
  branch (-1, +1)  →  Z correction
  branch (-1, -1)  →  Y correction (= iXZ; equal to X·Z up to global phase)

The pen-and-paper derivations are recorded in the comments above each
lemma; they are independently double-checked by
`qiskit/verify_chosen_gadgets.py`.
-/
import QMeas.Pauli
import QMeas.QState
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace QMeas
namespace Gadget.H

open Complex

/-- The input qubit state `α|0⟩ + β|1⟩` viewed as an element of `Vec 2`. -/
def psi (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => α
  | ⟨1, _⟩ => β

/-- The two-qubit initial state `|ψ⟩_q ⊗ |0⟩_a` in basis order
    `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def initState (α β : ℂ) : Vec 4
  | ⟨0, _⟩ => α   -- |00⟩
  | ⟨1, _⟩ => 0   -- |01⟩
  | ⟨2, _⟩ => β   -- |10⟩
  | ⟨3, _⟩ => 0   -- |11⟩

/-- After projecting on the +1 eigenspace of `Z⊗X` and renormalizing
    (probability is `1/2` whenever `|α|²+|β|² = 1`), the state on (q,a) is
    `(α/√2)|00⟩ + (α/√2)|01⟩ + (β/√2)|10⟩ - (β/√2)|11⟩`. -/
noncomputable def afterMeasZX_plus (α β : ℂ) : Vec 4
  | ⟨0, _⟩ =>  α / (Real.sqrt 2 : ℂ)
  | ⟨1, _⟩ =>  α / (Real.sqrt 2 : ℂ)
  | ⟨2, _⟩ =>  β / (Real.sqrt 2 : ℂ)
  | ⟨3, _⟩ => -β / (Real.sqrt 2 : ℂ)

/-- After projecting on the −1 eigenspace of `Z⊗X` and renormalizing. -/
noncomputable def afterMeasZX_minus (α β : ℂ) : Vec 4
  | ⟨0, _⟩ => -α / (Real.sqrt 2 : ℂ)   -- coefficient of |00⟩
  | ⟨1, _⟩ =>  α / (Real.sqrt 2 : ℂ)
  | ⟨2, _⟩ =>  β / (Real.sqrt 2 : ℂ)
  | ⟨3, _⟩ =>  β / (Real.sqrt 2 : ℂ)

/-- After both measurements `(r1=+1, r2=+1)`: the joint state factorizes as
    `|+⟩_q ⊗ ((α+β)|0⟩_a + (α-β)|1⟩_a)/√2`, so the state on `a` is exactly
    `H|ψ⟩`. -/
noncomputable def state_a_pp (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => (α + β) / (Real.sqrt 2 : ℂ)
  | ⟨1, _⟩ => (α - β) / (Real.sqrt 2 : ℂ)

/-- After both measurements `(r1=+1, r2=-1)`: state on `a` is `X·H|ψ⟩`. -/
noncomputable def state_a_pm (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => (α - β) / (Real.sqrt 2 : ℂ)
  | ⟨1, _⟩ => (α + β) / (Real.sqrt 2 : ℂ)

/-- After both measurements `(r1=-1, r2=+1)`: state on `a` is `Z·H|ψ⟩`. -/
noncomputable def state_a_mp (α β : ℂ) : Vec 2
  | ⟨0, _⟩ =>  (α + β) / (Real.sqrt 2 : ℂ)
  | ⟨1, _⟩ => -(α - β) / (Real.sqrt 2 : ℂ)

/-- After both measurements `(r1=-1, r2=-1)`: state on `a` is `Y·H|ψ⟩` (up to
    global phase). -/
noncomputable def state_a_mm (α β : ℂ) : Vec 2
  | ⟨0, _⟩ =>  (-(α - β)) / (Real.sqrt 2 : ℂ)
  | ⟨1, _⟩ =>  (α + β) / (Real.sqrt 2 : ℂ)

/-- The Hadamard applied to `|ψ⟩ = α|0⟩ + β|1⟩` is
    `((α+β)/√2)|0⟩ + ((α-β)/√2)|1⟩`. -/
theorem H_apply (α β : ℂ) :
    (H_gate *ᵥ psi α β) = state_a_pp α β := by
  funext i
  fin_cases i <;>
    simp [H_gate, psi, state_a_pp, applyOp, Matrix.smul_apply,
          Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Matrix.head_fin_const] <;>
    ring

/-- Branch (+1, +1): no Pauli correction needed, state on `a` equals `H|ψ⟩`. -/
theorem branch_pp_correct (α β : ℂ) :
    state_a_pp α β = (H_gate *ᵥ psi α β) := by
  exact (H_apply α β).symm

/-- Branch (+1, -1): applying `X` to the post-measurement state on `a` yields
    `H|ψ⟩`. -/
theorem branch_pm_correct (α β : ℂ) :
    σX *ᵥ state_a_pm α β = (H_gate *ᵥ psi α β) := by
  funext i
  fin_cases i <;>
    simp [σX, H_gate, psi, state_a_pm, applyOp, Matrix.smul_apply,
          Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons] <;>
    ring

/-- Branch (-1, +1): applying `Z` to the post-measurement state on `a` yields
    `H|ψ⟩`. -/
theorem branch_mp_correct (α β : ℂ) :
    σZ *ᵥ state_a_mp α β = (H_gate *ᵥ psi α β) := by
  funext i
  fin_cases i <;>
    simp [σZ, H_gate, psi, state_a_mp, applyOp, Matrix.smul_apply,
          Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons] <;>
    ring

/-- Branch (-1, -1): applying `Y` to the post-measurement state on `a` yields
    `H|ψ⟩` up to a global sign (which is unobservable). -/
theorem branch_mm_correct (α β : ℂ) :
    σY *ᵥ state_a_mm α β = (-Complex.I) • ((H_gate *ᵥ psi α β)) := by
  funext i
  fin_cases i <;>
    simp [σY, H_gate, psi, state_a_mm, applyOp, Matrix.smul_apply,
          Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Top-level QMeas H-gadget correctness: in every measurement branch, the
    state on the ancilla `a`, after applying the byproduct Pauli stored in
    the frame, equals `H|ψ⟩` (up to an unobservable global phase in the
    `(-1,-1)` branch).  The four `branch_*` lemmas above package the four
    cases.  -/
theorem H_gadget_correct (α β : ℂ) :
    state_a_pp α β              = (H_gate *ᵥ psi α β) ∧
    σX *ᵥ state_a_pm α β        = (H_gate *ᵥ psi α β) ∧
    σZ *ᵥ state_a_mp α β        = (H_gate *ᵥ psi α β) ∧
    σY *ᵥ state_a_mm α β        = (-Complex.I) • ((H_gate *ᵥ psi α β)) :=
  ⟨branch_pp_correct α β,
   branch_pm_correct α β,
   branch_mp_correct α β,
   branch_mm_correct α β⟩

end Gadget.H
end QMeas
