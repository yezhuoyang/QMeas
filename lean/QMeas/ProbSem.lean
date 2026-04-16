/-
# QMeas probabilistic operational semantics (reviewer R09).

Extends the nondeterministic `Step` relation of `Sem.lean` with
Born-rule measurement weights.
-/
import QMeas.Sem

namespace QMeas

open Complex

noncomputable def normSq {D : Nat} (v : Vec D) : ℝ :=
  ∑ i : Fin D, (Complex.normSq (v i) : ℝ)

noncomputable def bornWeight {D : Nat} (P : Op D) (s : ℤ) (ρ : Vec D) : ℝ :=
  let projected := postMeas P s ρ
  if normSq ρ = 0 then 0
  else normSq projected / normSq ρ

structure PStepResult (D : Nat) where
  obs    : Obs
  weight : ℝ
  config : Config D

inductive PStep {D : Nat} : Config D → PStepResult D → Prop where
  | silent (c c' : Config D) (obs : Obs) (h : Step c obs c') (ho : obs = .silent) :
      PStep c ⟨obs, 1, c'⟩
  | meas1_weighted (ρ : Vec D) (σ : Store) (F : Frame)
      (r : Nat) (P : Pauli1) (q : Nat) (s : Int) (hs : s = 1 ∨ s = -1)
      (mat : Op D) (w : ℝ) (hw : w = bornWeight mat s ρ) :
      PStep ⟨ρ, σ, F, .meas1 r P q⟩
            ⟨.meas s, w, ⟨postMeas1 P q s ρ, Store.set σ r s, F, .skip⟩⟩
  | meas2_weighted (ρ : Vec D) (σ : Store) (F : Frame)
      (r : Nat) (P : List Pauli1) (qa qb : Nat) (s : Int)
      (hs : s = 1 ∨ s = -1)
      (mat : Op D) (w : ℝ) (hw : w = bornWeight mat s ρ) :
      PStep ⟨ρ, σ, F, .meas2 r P qa qb⟩
            ⟨.meas s, w, ⟨postMeas2 P qa qb s ρ, Store.set σ r s, F, .skip⟩⟩

inductive PMultiStep {D : Nat} : Config D → List Obs → ℝ → Config D → Prop where
  | refl (c : Config D) : PMultiStep c [] 1 c
  | step (c₁ c₂ c₃ : Config D) (obs : Obs) (w : ℝ)
      (trace : List Obs) (cumWeight : ℝ)
      (h₁ : PStep c₁ ⟨obs, w, c₂⟩)
      (h₂ : PMultiStep c₂ trace cumWeight c₃) :
      PMultiStep c₁ (obs :: trace) (w * cumWeight) c₃

/-! ## Born-rule weights sum to 1 -/

theorem bornWeight_sum_one_of_proj {D : Nat} (P : Op D) (ρ : Vec D)
    (hProj : normSq (postMeas P 1 ρ) + normSq (postMeas P (-1) ρ) = normSq ρ)
    (hρ : normSq ρ ≠ 0) :
    bornWeight P 1 ρ + bornWeight P (-1) ρ = 1 := by
  simp only [bornWeight, if_neg hρ]
  show normSq (postMeas P 1 ρ) / normSq ρ + normSq (postMeas P (-1) ρ) / normSq ρ = 1
  rw [← add_div, hProj, div_self hρ]

private lemma postMeas_entry_σZ_0_pos (ρ : Vec 2) : postMeas σZ 1 ρ 0 = ρ 0 := by
  simp [postMeas, applyOp, projector, σZ, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

private lemma postMeas_entry_σZ_1_pos (ρ : Vec 2) : postMeas σZ 1 ρ 1 = 0 := by
  simp [postMeas, applyOp, projector, σZ, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

private lemma postMeas_entry_σZ_0_neg (ρ : Vec 2) : postMeas σZ (-1) ρ 0 = 0 := by
  simp [postMeas, applyOp, projector, σZ, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

private lemma postMeas_entry_σZ_1_neg (ρ : Vec 2) : postMeas σZ (-1) ρ 1 = ρ 1 := by
  simp [postMeas, applyOp, projector, σZ, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]

theorem projector_normSq_sum_σZ (ρ : Vec 2) :
    normSq (postMeas σZ 1 ρ) + normSq (postMeas σZ (-1) ρ) = normSq ρ := by
  simp only [normSq, Fin.sum_univ_two,
    postMeas_entry_σZ_0_pos, postMeas_entry_σZ_1_pos,
    postMeas_entry_σZ_0_neg, postMeas_entry_σZ_1_neg, map_zero]
  ring

private lemma postMeas_entry_σX_0_pos (ρ : Vec 2) :
    postMeas σX 1 ρ 0 = (ρ 0 + ρ 1) / 2 := by
  simp [postMeas, applyOp, projector, σX, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma postMeas_entry_σX_1_pos (ρ : Vec 2) :
    postMeas σX 1 ρ 1 = (ρ 0 + ρ 1) / 2 := by
  simp [postMeas, applyOp, projector, σX, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma postMeas_entry_σX_0_neg (ρ : Vec 2) :
    postMeas σX (-1) ρ 0 = (ρ 0 - ρ 1) / 2 := by
  simp [postMeas, applyOp, projector, σX, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma postMeas_entry_σX_1_neg (ρ : Vec 2) :
    postMeas σX (-1) ρ 1 = (ρ 1 - ρ 0) / 2 := by
  simp [postMeas, applyOp, projector, σX, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma normSq_half (z : ℂ) : Complex.normSq (z / 2) = Complex.normSq z / 4 := by
  rw [show z / (2:ℂ) = z * (2⁻¹ : ℂ) from div_eq_mul_inv z 2]
  rw [map_mul]
  simp [Complex.normSq_apply, Complex.inv_re, Complex.inv_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma parallelogram_normSq (a b : ℂ) :
    Complex.normSq (a + b) + Complex.normSq (a - b) =
    2 * (Complex.normSq a + Complex.normSq b) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
             Complex.sub_re, Complex.sub_im]
  ring

theorem projector_normSq_sum_σX (ρ : Vec 2) :
    normSq (postMeas σX 1 ρ) + normSq (postMeas σX (-1) ρ) = normSq ρ := by
  simp only [normSq, Fin.sum_univ_two,
    postMeas_entry_σX_0_pos, postMeas_entry_σX_1_pos,
    postMeas_entry_σX_0_neg, postMeas_entry_σX_1_neg]
  rw [show (ρ 1 - ρ 0) / 2 = -((ρ 0 - ρ 1) / 2) from by ring,
      Complex.normSq_neg]
  simp only [normSq_half]
  linarith [parallelogram_normSq (ρ 0) (ρ 1)]

private lemma postMeas_entry_σY_0_pos (ρ : Vec 2) :
    postMeas σY 1 ρ 0 = (ρ 0 - Complex.I * ρ 1) / 2 := by
  simp [postMeas, applyOp, projector, σY, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma postMeas_entry_σY_1_pos (ρ : Vec 2) :
    postMeas σY 1 ρ 1 = (ρ 1 + Complex.I * ρ 0) / 2 := by
  simp [postMeas, applyOp, projector, σY, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma postMeas_entry_σY_0_neg (ρ : Vec 2) :
    postMeas σY (-1) ρ 0 = (ρ 0 + Complex.I * ρ 1) / 2 := by
  simp [postMeas, applyOp, projector, σY, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

private lemma postMeas_entry_σY_1_neg (ρ : Vec 2) :
    postMeas σY (-1) ρ 1 = (ρ 1 - Complex.I * ρ 0) / 2 := by
  simp [postMeas, applyOp, projector, σY, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]; ring

theorem projector_normSq_sum_σY (ρ : Vec 2) :
    normSq (postMeas σY 1 ρ) + normSq (postMeas σY (-1) ρ) = normSq ρ := by
  simp only [normSq, Fin.sum_univ_two,
    postMeas_entry_σY_0_pos, postMeas_entry_σY_1_pos,
    postMeas_entry_σY_0_neg, postMeas_entry_σY_1_neg]
  rw [show (ρ 1 - Complex.I * ρ 0) / 2 = -((Complex.I * ρ 0 - ρ 1) / 2) from by ring,
      Complex.normSq_neg,
      show (Complex.I * ρ 0 - ρ 1) / 2 = -((ρ 1 - Complex.I * ρ 0) / 2) from by ring,
      Complex.normSq_neg,
      show (ρ 0 + Complex.I * ρ 1) / 2 = -((-(Complex.I * ρ 1) - ρ 0) / 2) from by ring,
      Complex.normSq_neg,
      show (-(Complex.I * ρ 1) - ρ 0) / 2 = -((ρ 0 - -(Complex.I * ρ 1)) / 2) from by ring,
      Complex.normSq_neg]
  simp only [normSq_half]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem bornWeight_sum_one_pauli1 (P : Pauli1) (ρ : Vec 2)
    (hρ : normSq ρ ≠ 0) :
    bornWeight (Frame.pauliMat P) 1 ρ + bornWeight (Frame.pauliMat P) (-1) ρ = 1 := by
  cases P
  · exact bornWeight_sum_one_of_proj _ ρ (projector_normSq_sum_σX ρ) hρ
  · exact bornWeight_sum_one_of_proj _ ρ (projector_normSq_sum_σY ρ) hρ
  · exact bornWeight_sum_one_of_proj _ ρ (projector_normSq_sum_σZ ρ) hρ

end QMeas
