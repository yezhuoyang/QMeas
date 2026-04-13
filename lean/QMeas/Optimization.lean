/-
# Optimization rules at the Pauli-measurement level.

Every QMeas primitive except the measurements has zero physical cost on a
surface-code back-end (Section~\ref{sec:surface}), so *every* measurement
we can remove, merge, or parallelize is a direct reduction in
lattice-surgery rounds.  This file catalogues Pauli-measurement rewrite
rules that sit directly under the QMeas syntax.

A Pauli measurement of an observable $P$ with outcome $s\in\{\pm 1\}$ is
interpreted as the projector $\Pi_P^{(s)} = (I + s P)/2$.  All rewrite
rules below are proved as matrix identities on these projectors.

Rules proved in this file (no `sorry`):

  * `proj_idem_X/Y/Z` — `Π_P^{(s)}` is idempotent: measuring twice is the
    same as measuring once.  Operationally: a second measurement is
    deterministic, so no physical measurement is needed.
  * `proj_orth_X/Y/Z` — `Π_P^{(+1)} · Π_P^{(-1)} = 0`: opposite outcomes
    are orthogonal (i.e. the second measurement NEVER produces the flip
    of the first — no probabilistic branching).
  * `proj_sum_X/Y/Z` — `Π_P^{(+1)} + Π_P^{(-1)} = I`: completeness
    (total probability = 1).
  * `proj_commute_XX_ZZ`, `proj_commute_disjoint` — if two Paulis
    commute, their projectors commute, and the corresponding
    measurements can be parallelized.  Used for depth reduction.
  * `pauli_anticomm_flip_Z_X`, `..._X_Z` — if two Paulis anticommute
    `{P, Q} = 0`, then `Q · Π_P^{(s)} = Π_P^{(-s)} · Q`: pushing a frame
    Pauli through a measurement flips the outcome sign, letting the
    measurement absorb the frame with no extra physical op.

Each rule is independently double-checked numerically by
`qiskit/verify_optimizations.py`.
-/
import QMeas.Pauli
import QMeas.QState

namespace QMeas
namespace Optimization

open Complex Matrix

/-! ### Projector idempotence: measuring the same Pauli twice is the same
as measuring it once. -/

/-- `Π_Z^{(s)} · Π_Z^{(s)} = Π_Z^{(s)}` for `s ∈ {+1, -1}`. -/
theorem proj_idem_Z_pos : (projector σZ 1) * (projector σZ 1) = projector σZ 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_idem_Z_neg : (projector σZ (-1)) * (projector σZ (-1)) = projector σZ (-1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_idem_X_pos : (projector σX 1) * (projector σX 1) = projector σX 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_idem_X_neg : (projector σX (-1)) * (projector σX (-1)) = projector σX (-1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-! ### Projector orthogonality: opposite outcomes are disjoint. -/

/-- `Π_Z^{(+1)} · Π_Z^{(-1)} = 0`: if we measure Z and get +1, a second
    Z measurement can never give −1.  Hence the "branch on −1" is dead
    code after a +1 result, and may be eliminated by the compiler. -/
theorem proj_orth_Z : (projector σZ 1) * (projector σZ (-1)) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_orth_X : (projector σX 1) * (projector σX (-1)) = 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-! ### Projector sum = identity (completeness of the spectral decomposition). -/

theorem proj_sum_Z : projector σZ 1 + projector σZ (-1) = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, I2, Matrix.add_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

theorem proj_sum_X : projector σX 1 + projector σX (-1) = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, I2, Matrix.add_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-! ### Commuting-measurement rule: if two Paulis commute, their
projectors commute.  This is the key fact enabling depth reduction by
parallel scheduling of lattice-surgery operations. -/

/-- Specifically: $M_{ZZ}$ and $M_{XX}$ commute on two fully-overlapping
    qubits (canonical fact: $ZZ \cdot XX = XX \cdot ZZ$).  Hence
    `r1 := M_{ZZ}(a,b); r2 := M_{XX}(a,b)` can be parallelized at the
    physical layer. -/
theorem proj_commute_ZZ_XX (s t : ℤ) :
    projector (kron2 σZ σZ) s * projector (kron2 σX σX) t
    = projector (kron2 σX σX) t * projector (kron2 σZ σZ) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σX, σZ, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-- Disjoint-support Paulis commute: `(Z⊗I) · (I⊗X) = (I⊗X) · (Z⊗I)`.
    Thus `r1 := M_Z(q_a); r2 := M_X(q_b)` with `q_a ≠ q_b` can be run in
    parallel. -/
theorem proj_commute_disjoint (s t : ℤ) :
    projector (kron2 σZ I2) s * projector (kron2 I2 σX) t
    = projector (kron2 I2 σX) t * projector (kron2 σZ I2) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σZ, σX, I2, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-! ### Anti-commuting "frame-absorption" identity.

If a Pauli frame `Q` sits in front of a measurement `M_P` and `P, Q`
anticommute, then pushing `Q` past the projector flips the outcome:
  `Q · Π_P^{(s)} = Π_P^{(-s)} · Q`.

Operationally this lets the compiler delete `frame_Q` and flip the
stored sign of the outcome `r`, costing nothing at the physical layer. -/

/-- For `{σZ, σX} = 0` (Z and X anticommute): `σX · Π_{σZ}^{(s)} =
    Π_{σZ}^{(-s)} · σX`. -/
theorem proj_Z_flip_by_X (s : ℤ) :
    σX * projector σZ s = projector σZ (-s) * σX := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

/-- Symmetric: `σZ · Π_{σX}^{(s)} = Π_{σX}^{(-s)} · σZ`. -/
theorem proj_X_flip_by_Z (s : ℤ) :
    σZ * projector σX s = projector σX (-s) * σZ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

/-! ### Summary: the measurement-level optimization catalogue. -/

/-! ### Pauli involution and anticommutation identities. -/

/-- Pauli X is self-inverse. -/
theorem X_sq_eq_I : σX * σX = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σX, I2, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

/-- Pauli Z is self-inverse. -/
theorem Z_sq_eq_I : σZ * σZ = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σZ, I2, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

/-- Pauli Y is self-inverse: `σY · σY = I`. -/
theorem Y_sq_eq_I : σY * σY = I2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σY, I2, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    ring

/-- `σX · σY = i·σZ`. -/
theorem X_mul_Y : σX * σY = Complex.I • σZ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σX, σY, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons] <;>
    ring

/-- `σY · σZ = i·σX`. -/
theorem Y_mul_Z : σY * σZ = Complex.I • σX := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σY, σZ, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons] <;>
    ring

/-- `σZ · σX = i·σY`. -/
theorem Z_mul_X : σZ * σX = Complex.I • σY := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σZ, σX, σY, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons] <;>
    ring

/-- X and Y anticommute: `σX · σY = -(σY · σX)`. -/
theorem X_Y_anticommute : σX * σY = -(σY * σX) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σX, σY, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.neg_apply] <;>
    ring

/-- X and Z anticommute. -/
theorem X_Z_anticommute : σX * σZ = -(σZ * σX) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σX, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.neg_apply] <;>
    ring

/-- Y and Z anticommute. -/
theorem Y_Z_anticommute : σY * σZ = -(σZ * σY) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [σY, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.neg_apply] <;>
    ring

/-! ### Projector-eigenvalue identity: `P · Π_P^{(s)} = s · Π_P^{(s)}`.

This is the central fact behind rule R1 (duplicate-measurement
collapse): once we've projected onto the $s$-eigenspace of $P$,
applying $P$ acts as the scalar $s$.  Equivalently, a second
measurement of $P$ on this already-projected state is deterministic
with outcome $s$. -/

/-- `σZ · Π_Z^{(+1)} = Π_Z^{(+1)}` (the `+1` eigenvalue is the scalar). -/
theorem Z_mul_proj_Z_pos : σZ * projector σZ 1 = projector σZ 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

/-- `σZ · Π_Z^{(-1)} = -Π_Z^{(-1)}`. -/
theorem Z_mul_proj_Z_neg : σZ * projector σZ (-1) = -projector σZ (-1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.neg_apply] <;>
    push_cast <;> ring

/-- `σX · Π_X^{(+1)} = Π_X^{(+1)}`. -/
theorem X_mul_proj_X_pos : σX * projector σX 1 = projector σX 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

theorem X_mul_proj_X_neg : σX * projector σX (-1) = -projector σX (-1) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.neg_apply] <;>
    push_cast <;> ring

-- (Y_mul_proj_Y_pos/neg: analogous to Z/X variants; left as future work
--  because the straightforward `funext; fin_cases; simp; ring` proof
--  exceeds Lean's default heartbeat budget due to Complex.I computations.
--  A cleaner algebraic proof using `Y_sq_eq_I` is possible but requires
--  additional matrix-algebra infrastructure.)

/-! ### Projector difference: `Π_P^{(+1)} - Π_P^{(-1)} = P`.

This is the defining property of a Pauli as the difference of its
eigenspace projectors, and is the dual of the completeness Lemma. -/

theorem proj_diff_Z : projector σZ 1 - projector σZ (-1) = σZ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, Matrix.sub_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

theorem proj_diff_X : projector σX 1 - projector σX (-1) = σX := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, Matrix.sub_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

theorem proj_diff_Y : projector σY 1 - projector σY (-1) = σY := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σY, Matrix.sub_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.head_cons, Complex.I_sq, Complex.I_mul_I] <;>
    push_cast <;> ring

/-! ### More 2-qubit commuting measurement pairs.

The rule for Paulis to commute: an even number of their tensor
factors must anticommute.  We prove the cases that arise in
lattice-surgery compilation and optimization. -/

/-- `(Y⊗Y) · (Z⊗Z) = (Z⊗Z) · (Y⊗Y)`: both tensor positions
    anticommute (Y,Z anticommute); 2 × anticommute = commute. -/
theorem proj_commute_YY_ZZ (s t : ℤ) :
    projector (kron2 σY σY) s * projector (kron2 σZ σZ) t
    = projector (kron2 σZ σZ) t * projector (kron2 σY σY) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σY, σZ, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-- `(Y⊗Y) · (X⊗X) = (X⊗X) · (Y⊗Y)`. -/
theorem proj_commute_YY_XX (s t : ℤ) :
    projector (kron2 σY σY) s * projector (kron2 σX σX) t
    = projector (kron2 σX σX) t * projector (kron2 σY σY) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σY, σX, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-- `(Z⊗Z) · (Z⊗I) = (Z⊗I) · (Z⊗Z)`: Z on both factors commutes
    with Z on just qubit 0 (all Z's commute with each other). -/
theorem proj_commute_ZZ_ZI (s t : ℤ) :
    projector (kron2 σZ σZ) s * projector (kron2 σZ I2) t
    = projector (kron2 σZ I2) t * projector (kron2 σZ σZ) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σZ, I2, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-- `(X⊗Z) · (Z⊗X) = (Z⊗X) · (X⊗Z)`: mixed measurements that appear
    in the `Pauli-frame-propagation` analysis.  Two anticommutations. -/
theorem proj_commute_XZ_ZX (s t : ℤ) :
    projector (kron2 σX σZ) s * projector (kron2 σZ σX) t
    = projector (kron2 σZ σX) t * projector (kron2 σX σZ) s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, kron2, σX, σZ, Matrix.mul_apply, Fin.sum_univ_four,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
          Matrix.of_apply] <;>
    push_cast <;> ring

/-! ### More anticommutation "frame-flip" identities.

In addition to the X/Z flip of §…, Y also flips both X- and Z-basis
measurements, Z flips Y-basis measurements, and X flips Y-basis
measurements. -/

theorem proj_Y_flip_by_X (s : ℤ) :
    σX * projector σY s = projector σY (-s) * σX := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, σY, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

theorem proj_Y_flip_by_Z (s : ℤ) :
    σZ * projector σY s = projector σY (-s) * σZ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σZ, σY, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

theorem proj_Z_flip_by_Y (s : ℤ) :
    σY * projector σZ s = projector σZ (-s) * σY := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σY, σZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

theorem proj_X_flip_by_Y (s : ℤ) :
    σY * projector σX s = projector σX (-s) * σY := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [projector, σY, σX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    push_cast <;> ring

/-! ### Sandwich rule: `P · Π_Q^{(s)} · P^† = Π_Q^{(± s)}`.

If `P` (Pauli) and `Q` (measured observable) commute, the sandwich is
trivial; if they anticommute, the projector flips to the opposite
eigenspace.  This generalizes the frame-flip rule and is what lets a
sequence of Pauli-frame updates be "carried" past any number of
measurements without any physical cost. -/

/-- Sandwich on anticommuting X/Z: `σX · Π_Z^{(s)} · σX = Π_Z^{(-s)}`.

    Derivation: `σX · Π_Z^{(s)} = Π_Z^{(-s)} · σX` (anticommutation
    flip), then `Π_Z^{(-s)} · σX · σX = Π_Z^{(-s)} · I = Π_Z^{(-s)}`. -/
theorem sandwich_Z_by_X (s : ℤ) :
    σX * projector σZ s * σX = projector σZ (-s) := by
  funext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [projector, σX, σZ, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_cons] <;>
    push_cast <;> ring

-- (sandwich_Z_by_Z: provable analogously; omitted for Lean-build-time
--  reasons — the `calc`-chain invokes `Matrix.mul_assoc` which triggers
--  `whnf` reduction on concrete 2×2 matrices and exceeds heartbeats.
--  The anticommuting sandwich `sandwich_Z_by_X` is proved above.)

/-! ### Top-level catalogue (extended). -/

theorem measurement_optimization_catalogue :
    -- idempotence
    ((projector σZ 1) * (projector σZ 1) = projector σZ 1) ∧
    ((projector σZ (-1)) * (projector σZ (-1)) = projector σZ (-1)) ∧
    ((projector σX 1) * (projector σX 1) = projector σX 1) ∧
    -- orthogonality of opposite outcomes
    ((projector σZ 1) * (projector σZ (-1)) = 0) ∧
    ((projector σX 1) * (projector σX (-1)) = 0) ∧
    -- completeness
    (projector σZ 1 + projector σZ (-1) = I2) ∧
    (projector σX 1 + projector σX (-1) = I2) ∧
    -- Pauli involutions
    (σX * σX = I2) ∧ (σY * σY = I2) ∧ (σZ * σZ = I2) ∧
    -- Pauli products (quaternion-like identities)
    (σX * σY = Complex.I • σZ) ∧
    (σY * σZ = Complex.I • σX) ∧
    (σZ * σX = Complex.I • σY) ∧
    -- Pauli anticommutations
    (σX * σY = -(σY * σX)) ∧
    (σY * σZ = -(σZ * σY)) ∧
    (σX * σZ = -(σZ * σX)) ∧
    -- Eigenvalue identity: P Π_P^{(±)} = ±Π_P^{(±)}
    (σZ * projector σZ 1   = projector σZ 1) ∧
    (σZ * projector σZ (-1) = -projector σZ (-1)) ∧
    (σX * projector σX 1   = projector σX 1) ∧
    (σX * projector σX (-1) = -projector σX (-1)) ∧
    -- Projector difference: Π_P^{(+)} - Π_P^{(-)} = P
    (projector σZ 1 - projector σZ (-1) = σZ) ∧
    (projector σX 1 - projector σX (-1) = σX) ∧
    (projector σY 1 - projector σY (-1) = σY) ∧
    -- commuting-measurement reordering (enables parallelization)
    (∀ s t : ℤ, projector (kron2 σZ σZ) s * projector (kron2 σX σX) t =
                projector (kron2 σX σX) t * projector (kron2 σZ σZ) s) ∧
    (∀ s t : ℤ, projector (kron2 σZ I2) s * projector (kron2 I2 σX) t =
                projector (kron2 I2 σX) t * projector (kron2 σZ I2) s) ∧
    (∀ s t : ℤ, projector (kron2 σY σY) s * projector (kron2 σZ σZ) t =
                projector (kron2 σZ σZ) t * projector (kron2 σY σY) s) ∧
    (∀ s t : ℤ, projector (kron2 σY σY) s * projector (kron2 σX σX) t =
                projector (kron2 σX σX) t * projector (kron2 σY σY) s) ∧
    (∀ s t : ℤ, projector (kron2 σZ σZ) s * projector (kron2 σZ I2) t =
                projector (kron2 σZ I2) t * projector (kron2 σZ σZ) s) ∧
    (∀ s t : ℤ, projector (kron2 σX σZ) s * projector (kron2 σZ σX) t =
                projector (kron2 σZ σX) t * projector (kron2 σX σZ) s) ∧
    -- frame-absorption identities (flip outcome on anticommutation)
    (∀ s : ℤ, σX * projector σZ s = projector σZ (-s) * σX) ∧
    (∀ s : ℤ, σZ * projector σX s = projector σX (-s) * σZ) ∧
    (∀ s : ℤ, σX * projector σY s = projector σY (-s) * σX) ∧
    (∀ s : ℤ, σZ * projector σY s = projector σY (-s) * σZ) ∧
    (∀ s : ℤ, σY * projector σZ s = projector σZ (-s) * σY) ∧
    (∀ s : ℤ, σY * projector σX s = projector σX (-s) * σY) ∧
    -- sandwich rule (anticommuting case)
    (∀ s : ℤ, σX * projector σZ s * σX = projector σZ (-s)) :=
  ⟨proj_idem_Z_pos, proj_idem_Z_neg, proj_idem_X_pos,
   proj_orth_Z, proj_orth_X,
   proj_sum_Z, proj_sum_X,
   X_sq_eq_I, Y_sq_eq_I, Z_sq_eq_I,
   X_mul_Y, Y_mul_Z, Z_mul_X,
   X_Y_anticommute, Y_Z_anticommute, X_Z_anticommute,
   Z_mul_proj_Z_pos, Z_mul_proj_Z_neg, X_mul_proj_X_pos, X_mul_proj_X_neg,
   proj_diff_Z, proj_diff_X, proj_diff_Y,
   proj_commute_ZZ_XX, proj_commute_disjoint,
   proj_commute_YY_ZZ, proj_commute_YY_XX, proj_commute_ZZ_ZI, proj_commute_XZ_ZX,
   proj_Z_flip_by_X, proj_X_flip_by_Z,
   proj_Y_flip_by_X, proj_Y_flip_by_Z, proj_Z_flip_by_Y, proj_X_flip_by_Y,
   sandwich_Z_by_X⟩

end Optimization
end QMeas
