/-
# T-gadget --- formal correctness statement.

The QMeas T-gadget realizes the non-Clifford $T$ gate via injection of an
$|A\rangle = T|+\rangle = (|0\rangle + e^{i\pi/4}|1\rangle)/\sqrt 2$ magic
state.  The program is:

```
ancilla m holds |A>
r1 := M_{ZZ}(q, m)
r2 := M_X(q)
if r1 == -1 : invoke S-gadget on m       -- Clifford byproduct
if r1 == +1 ∧ r2 == -1 : frame_Z(m)
if r1 == -1 ∧ r2 == +1 : frame_X(m)
if r1 == -1 ∧ r2 == -1 : frame_Y(m)
discard q
```

For an arbitrary input `|ψ⟩ = α|0⟩ + β|1⟩` on `q` and the four possible
measurement outcomes `(r1, r2) ∈ {±1}^2`, the post-measurement state
on `m`, after applying the byproduct (Pauli or Clifford) recorded in
the frame and the S-gadget, equals `T|ψ⟩` up to a known global phase
(unobservable on the encoded qubit).

We prove each of the four branches:

  branch (+1, +1)  →  no correction; state = (1/2) T|ψ⟩
  branch (+1, -1)  →  Z correction;   Z·state = (1/2) T|ψ⟩
  branch (-1, +1)  →  S·X correction; (S·X)·state = (ω/2) T|ψ⟩
  branch (-1, -1)  →  S·Y correction; (S·Y)·state = (ω*/2) T|ψ⟩

The `(-,+)` and `(-,-)` branches incur a global phase $\omega = e^{i\pi/4}$
or $\omega^* = e^{-i\pi/4}$, which is unobservable.  The S-gadget (proved
in `Gadgets.S`) realizes the Clifford $S$ inside QMeas using only Pauli
measurements, so the composite "S-gadget then frame_X / frame_Y" remains
a QMeas program.
-/
import QMeas.Pauli
import QMeas.QState
import QMeas.Cultivation

namespace QMeas
namespace Gadget.T

open Complex Cultivation

/-- The input qubit state $\alpha|0\rangle + \beta|1\rangle$. -/
def psi (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => α
  | ⟨1, _⟩ => β

/-- The magic state $|A\rangle = T|+\rangle = (|0\rangle + \omega|1\rangle)/\sqrt 2$.
    Equals `Cultivation.T_state`. -/
noncomputable def A_state : Vec 2 := T_state

/-- After both measurements `(r1=+1, r2=+1)`: state on $m$ is $\frac12 T|\psi\rangle$. -/
noncomputable def state_m_pp (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => α / 2
  | ⟨1, _⟩ => β * omega / 2

/-- After both measurements `(r1=+1, r2=-1)`: state on $m$ is $\frac12 Z\,T|\psi\rangle$. -/
noncomputable def state_m_pm (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => α / 2
  | ⟨1, _⟩ => -(β * omega) / 2

/-- After both measurements `(r1=-1, r2=+1)`: state on $m$ is $\frac1{2\omega} S\!X\,T|\psi\rangle$. -/
noncomputable def state_m_mp (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => β / 2
  | ⟨1, _⟩ => α * omega / 2

/-- After both measurements `(r1=-1, r2=-1)`: state on $m$ is $\frac{-1}{2\omega^*} S\!Y\,T|\psi\rangle$. -/
noncomputable def state_m_mm (α β : ℂ) : Vec 2
  | ⟨0, _⟩ => -β / 2
  | ⟨1, _⟩ => α * omega / 2

/-- Branch `(+1, +1)`: no correction; the state on $m$ equals $\frac12 T|\psi\rangle$. -/
theorem branch_pp_correct (α β : ℂ) :
    state_m_pp α β = (1/2 : ℂ) • applyOp T_gate (psi α β) := by
  funext i
  fin_cases i <;>
    simp [state_m_pp, T_gate, psi, applyOp, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Branch `(+1, -1)`: $Z$ correction recovers $\frac12 T|\psi\rangle$. -/
theorem branch_pm_correct (α β : ℂ) :
    applyOp σZ (state_m_pm α β) = (1/2 : ℂ) • applyOp T_gate (psi α β) := by
  funext i
  fin_cases i <;>
    simp [state_m_pm, T_gate, σZ, psi, applyOp, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Branch `(-1, +1)`: $S\!X$ correction recovers $\frac\omega2 T|\psi\rangle$ (global phase $\omega$).

    Uses the algebraic fact $\omega^2 = i$ (mechanized as
    `Cultivation.omega_mul_omega`). -/
theorem branch_mp_correct (α β : ℂ) :
    applyOp (S_gate * σX) (state_m_mp α β) = (omega / 2 : ℂ) • applyOp T_gate (psi α β) := by
  have hω2 : omega^2 = Complex.I := by rw [pow_two]; exact omega_mul_omega
  funext i
  fin_cases i
  · simp [state_m_mp, T_gate, S_gate, σX, psi, applyOp,
          Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one,
          Pi.smul_apply, smul_eq_mul]
    ring
  · simp [state_m_mp, T_gate, S_gate, σX, psi, applyOp,
          Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one,
          Pi.smul_apply, smul_eq_mul]
    linear_combination -(β / 2 : ℂ) * hω2

/-- Branch `(-1, -1)`: $S\!Y$ correction recovers $\frac{\omega^*}2 T|\psi\rangle$ (global phase $\omega^*$).

    Uses $\omega \cdot \overline\omega = 1$ (mechanized as
    `Cultivation.omega_mul_conj`). -/
theorem branch_mm_correct (α β : ℂ) :
    applyOp (S_gate * σY) (state_m_mm α β) =
      (starRingEnd ℂ omega / 2 : ℂ) • applyOp T_gate (psi α β) := by
  -- Unfold omega and starRingEnd explicitly, then reduce to a complex-arithmetic
  -- identity involving only Complex.I and (Real.sqrt 2 : ℂ).
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    have := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    exact_mod_cast this
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  have hsq2 : ((Real.sqrt 2 : ℂ))^2 = (2 : ℂ) := by
    rw [pow_two]; exact hsq
  funext i
  fin_cases i <;>
    simp [state_m_mm, T_gate, S_gate, σY, psi, applyOp,
          Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one,
          Pi.smul_apply, smul_eq_mul,
          omega, map_div₀, map_add, map_one, Complex.conj_I,
          Complex.conj_ofReal] <;>
    · field_simp
      ring_nf
      simp [hsq2, Complex.I_sq]
      try ring

/-- **Top-level T-gadget correctness.**  In every measurement branch,
    the state on the magic-state ancilla $m$, after applying the byproduct
    (Pauli or $S$-gadget-derived Clifford) recorded in the frame, equals
    $T|\psi\rangle$ up to a known global phase (unobservable on the
    encoded qubit).  The four `branch_*_correct` lemmas package the
    four cases. -/
theorem T_gadget_correct (α β : ℂ) :
    state_m_pp α β
      = (1/2 : ℂ) • applyOp T_gate (psi α β) ∧
    applyOp σZ (state_m_pm α β)
      = (1/2 : ℂ) • applyOp T_gate (psi α β) ∧
    applyOp (S_gate * σX) (state_m_mp α β)
      = (omega / 2 : ℂ) • applyOp T_gate (psi α β) ∧
    applyOp (S_gate * σY) (state_m_mm α β)
      = (starRingEnd ℂ omega / 2 : ℂ) • applyOp T_gate (psi α β) :=
  ⟨branch_pp_correct α β,
   branch_pm_correct α β,
   branch_mp_correct α β,
   branch_mm_correct α β⟩

end Gadget.T
end QMeas
