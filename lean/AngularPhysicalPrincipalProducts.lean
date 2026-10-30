import AngularPhysicalDetectorHighCorrection
import OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalPrincipalProducts
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

def idealMarkedClosed (η : AngularCharacter) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let R := coordR Q (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) x z
  markedFactor R (coordV Q z) (Q:ℂ)⁻¹ (coordK Q (η.idealHom P.val) x w)
    (-coordD Q (η.idealHom P.val) 1 x+coordW Q 1 w*R) 1

private theorem angular_local_defect (η : AngularCharacter) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖PhysicalDetectorHigh.idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P :=
  PhysicalDetectorHigh.remainder_idealClosedCorrection_bound η P hP x w z
    (PhysicalDetectorHigh.theta_bounds.2.le.trans hx) hw hz

private theorem angular_global_defect (η : AngularCharacter) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖PhysicalDetectorHigh.globalClosedCorrection η S x w z-1‖≤1/2 :=
  PhysicalDetectorHigh.remainder_globalClosedCorrection_bound η S hS x w z
    (PhysicalDetectorHigh.theta_bounds.2.le.trans hx) hw hz

private theorem angular_global_analytic_w (η : AngularCharacter) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>PhysicalDetectorHigh.globalClosedCorrection η S x w z)
      {w : ℂ|9/10<w.re} :=
  PhysicalDetectorHigh.remainder_globalClosedCorrection_analytic_w η S hS x z
    (PhysicalDetectorHigh.theta_bounds.2.le.trans hx) hz

private theorem angular_global_analytic_z (η : AngularCharacter) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 7/8≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>PhysicalDetectorHigh.globalClosedCorrection η S x w z)
      {z : ℂ|4/25<z.re} :=
  PhysicalDetectorHigh.remainder_globalClosedCorrection_analytic_z η S hS x w
    (PhysicalDetectorHigh.theta_bounds.2.le.trans hx) hw

def localMultiplier (η : AngularCharacter) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  (Q : ℂ)^(z-1) *
    (compensatedReplacement (coordV Q z) (coordW Q 1 w)
      (coordD Q (η.idealHom P.val) 1 x) (idealMarkedClosed η P x w z)
      (star (η.idealHom P.val)*(Q : ℂ)^x) ((Q : ℂ)^(-w)) /
      PhysicalDetectorHigh.idealClosedCorrection η P x w z)

def selectedMultiplier (η : AngularCharacter) (T : Finset PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∏ P ∈ T, localMultiplier η P x w z

def slotMultiplier {ι : Type*} (η : AngularCharacter) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (x w z : ℂ) : ℂ :=
  ∏ j ∈ J, ∑ P ∈ T j, b j P * localMultiplier η P x w z

theorem correction_lower_bound (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖PhysicalDetectorHigh.idealClosedCorrection η P x w z‖ := by
  have hb := (angular_local_defect η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (PhysicalDetectorHigh.idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    PhysicalDetectorHigh.idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(PhysicalDetectorHigh.idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖PhysicalDetectorHigh.idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma marked_differentiableAt_w (η : AngularCharacter) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (η.idealHom P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z (η : AngularCharacter) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx hz
  have hc := unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => PhysicalDetectorHigh.idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x w hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx hz.le
  have hmc := marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => PhysicalDetectorHigh.idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : 7/8 ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

def localBound (Bx Bz : ℝ) (P : PrimeIdeal) : ℝ :=
  (Ideal.absNorm P.val : ℝ)^(Bz-1) * (400*(1+(Ideal.absNorm P.val : ℝ)^Bx))

lemma localBound_nonneg (Bx Bz : ℝ) (P : PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem local_norm_bound (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (η.idealHom P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (AngularCharacter.norm_idealHom_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (η.idealHom P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (AngularCharacter.norm_idealHom_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound Q (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) x w z hQ
      (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

def selectedBound (T : Finset PrimeIdeal) (Bx Bz : ℝ) : ℝ :=
  ∏ P ∈ T, localBound Bx Bz P

def slotBound {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : ℝ :=
  ∏ j ∈ J, ∑ P ∈ T j, ‖b j P‖ * localBound Bx Bz P

lemma selectedBound_nonneg (T : Finset PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => localBound_nonneg Bx Bz P)

lemma slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg Bx Bz P))

theorem selected_analytic_w (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem selected_analytic_z (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem slot_analytic_w {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem selected_norm_bound (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem slot_norm_bound {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖PhysicalDetectorHigh.globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := angular_global_defect η S hS x w z hx hw hz
  have hn := norm_add_le (PhysicalDetectorHigh.globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => PhysicalDetectorHigh.globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (angular_global_analytic_w η S hS x z hx hz).mul (slot_analytic_w η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => PhysicalDetectorHigh.globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (angular_global_analytic_z η S hS x w hx hw).mul (slot_analytic_z η S hS J T b hT x w hx hw)

theorem combined_slot_bound {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖PhysicalDetectorHigh.globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem local_eq_regionSlot (η : AngularCharacter) (P : PrimeIdeal) (s w z : ℂ) :
    localMultiplier η P s w z = (Ideal.absNorm P.val : ℂ)^(z-1) *
      PrincipalSlotEstimate.regionSlot (Ideal.absNorm P.val)
        (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) s w z := by
  simp only [localMultiplier,PrincipalSlotEstimate.regionSlot,PrincipalSlotEstimate.regionReplacement,
    PrincipalSlotEstimate.regionMarked,idealMarkedClosed,PhysicalDetectorHigh.idealClosedCorrection,Complex.ofReal_natCast]

def windowMultiplier {ι : Type*} (η : AngularCharacter) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℂ) (scale : ι → ℝ) (s w z : ℂ) : ℂ :=
  slotMultiplier η J T (fun j P => W j ((Ideal.absNorm P.val : ℝ)/scale j)) s w z

theorem window_at_residue {ι : Type*} (η : AngularCharacter) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℝ) (scale : ι → ℝ) (s : ℂ) :
    windowMultiplier η J T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      ∏ j ∈ J, ∑ P ∈ T j,
        ((W j ((Ideal.absNorm P.val : ℝ)/scale j) *
          (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ)) : ℝ) : ℂ) *
        PrincipalSlotEstimate.principalSlot (Ideal.absNorm P.val)
          (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) s := by
  unfold windowMultiplier slotMultiplier
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro P hp
  rw [local_eq_regionSlot,PrincipalSlotEstimate.region_slot_at_residue]
  have hQ : 0 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hQ.le]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num
  ring_nf

theorem slot_norm_bound_sharp {ι : Type*} (η : AngularCharacter) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖η.idealHom P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using PrincipalSlotEstimate.weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val))
    (fun P => η.idealHom P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem combined_slot_bound_sharp {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖η.idealHom P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖PhysicalDetectorHigh.globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)

@[simp] theorem slotMultiplier_empty {ι : Type*} (η : AngularCharacter) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (s w z : ℂ) : slotMultiplier η ∅ T b s w z = 1 := by
  simp [slotMultiplier]

theorem selected_as_slots (η : AngularCharacter) (T : Finset PrimeIdeal) (s w z : ℂ) :
    selectedMultiplier η T s w z = slotMultiplier η T (fun P => {P}) (fun _ _ => 1) s w z := by
  simp [selectedMultiplier,slotMultiplier]

theorem uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : AngularCharacter) (s w z : ℂ),
      s.re ∈ Icc (7/8) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖PhysicalDetectorHigh.globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩


end OAI.SevenEighths.Angular.PhysicalPrincipalProducts

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.correction_lower_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.correction_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.correction_inverse_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.marked_differentiableAt_w

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.marked_differentiableAt_z

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.local_analytic_w

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.local_analytic_z

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.marked_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.replacement_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.localBound_nonneg

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.local_norm_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.selectedBound_nonneg

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.slotBound_nonneg

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.selected_analytic_w

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.selected_analytic_z

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.slot_analytic_w

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.slot_analytic_z

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.selected_norm_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.slot_norm_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.global_norm_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.combined_slot_analytic_w

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.combined_slot_analytic_z

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.combined_slot_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.local_eq_regionSlot

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.window_at_residue

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.slot_norm_bound_sharp

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.combined_slot_bound_sharp

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.selected_as_slots

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.uniform_closed_box_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalProducts.uniform_closed_box_bound
