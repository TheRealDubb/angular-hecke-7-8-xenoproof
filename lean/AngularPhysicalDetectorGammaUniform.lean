import AngularPhysicalDetectorGammaCutoff
import AngularPhysicalDetectorScale

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace OAI.SevenEighths.Angular.PhysicalGammaDetector
open FamilyContinuation GammaZeroDetector
theorem original_right_growth (angularOrder : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : AngularCharacter, χ.k.natAbs ≤ angularOrder →
      (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ s : ℂ,
      (1/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤
        C*(χ.modulus.absNorm : ℝ)^2*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hb⟩ := PhysicalDetectorDyadic.original_upper_strip angularOrder (1/10) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro χ horder hn s hs
  have hh := hb χ horder hn s (by linarith)
  have hq := PhysicalLogarithmic.modulus_norm_ge_one χ
  have hqp : (0:ℝ)<χ.modulus.absNorm := by linarith
  have hr := PhysicalDetectorDyadic.radical_norm_le_modulus χ
  have hc : (χ.modulus.absNorm : ℝ)^(3/5:ℝ)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+(1/10:ℝ)) ≤
      (χ.modulus.absNorm : ℝ)^2 := by
    calc
      _ ≤ (χ.modulus.absNorm : ℝ)^(3/5:ℝ)*(χ.modulus.absNorm : ℝ)^(1/10+(1/10:ℝ)) := by
        gcongr
      _ = (χ.modulus.absNorm : ℝ)^(4/5:ℝ) := by rw [←Real.rpow_add hqp]; norm_num
      _ ≤ (χ.modulus.absNorm : ℝ)^2 := by
        rw [←Real.rpow_two]
        exact Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
  apply hh.trans
  calc
    _ = C*((χ.modulus.absNorm : ℝ)^(3/5:ℝ)*
        ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+(1/10:ℝ)))*(3+|s.im|)^2 := by ring
    _ ≤ _ := by gcongr

theorem shifted_original_growth (angularOrder : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : AngularCharacter), χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ (ρ z : ℂ),
      (51/100 : ℝ) ≤ ρ.re → -(1/4 : ℝ) ≤ z.re →
      ‖LFunction χ (ρ+z)‖ ≤
        (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2)*(1+|z.im|)^2 := by
  obtain ⟨C,hC,hbound⟩ := original_right_growth angularOrder
  refine ⟨C,hC,?_⟩
  intro χ horder hχ ρ z hρ hz
  have hb := hbound χ horder hχ (ρ+z) (by simp only [add_re]; linarith)
  have hh : 3+|(ρ+z).im| ≤ (3+|ρ.im|)*(1+|z.im|) := by
    simp only [add_im]
    have hab := abs_add_le ρ.im z.im
    nlinarith [abs_nonneg ρ.im, abs_nonneg z.im]
  calc
    _ ≤ C*(χ.modulus.absNorm : ℝ)^2*((3+|ρ.im|)*(1+|z.im|))^2 := by
      apply hb.trans; gcongr
    _ = _ := by ring

def detectorIntegrand (χ : AngularCharacter) (V : ℝ → ℂ) (D Y : ℝ) (ρ z : ℂ) : ℂ :=
  (Y : ℂ)^z * Gamma z * LFunction χ (ρ+z) * cutoff χ V D (ρ+z)

def detectorIntegral (χ : AngularCharacter) (V : ℝ → ℂ) (D Y : ℝ) (ρ : ℂ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)

theorem detector_contour_shift (χ : AngularCharacter) (hχ : (χ.k ≠ 0 ∨ χ.residue ≠ 1))
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) :
    (∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) =
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (-(1/4)+t*I) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth χ.k.natAbs
  apply literal_contour_shift (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    ((PhysicalAnalytic.nonprincipal_entire χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY 2 (by positivity) (by positivity : 0 ≤ 256*D)
  · intro z hz _
    exact hgrowth χ (le_refl _) hχ ρ z hρ hz
  · intro z hz _
    exact cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith)

theorem detector_integral_bound (angularOrder : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : AngularCharacter), χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) →
      ∀ (V : ℝ → ℂ), (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (D Y : ℝ),
      1 ≤ D → 1 ≤ Y → ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 →
      ‖detectorIntegral χ V D Y ρ‖ ≤
        K*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2*D*Y^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth angularOrder
  obtain ⟨G,hG,hgamma⟩ := literal_detector_bound 2
  refine ⟨128*G*C, by positivity, ?_⟩
  intro χ horder hχ V hV D Y hD hY ρ hρ hzero
  have hb := hgamma (fun z => LFunction χ (ρ+z)) (fun z => cutoff χ V D (ρ+z))
    Y (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (256*D)
    ((PhysicalAnalytic.nonprincipal_entire χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ horder hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (by simp only [add_re]; linarith))
  change ‖∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)‖ ≤ _ at hb
  rw [detectorIntegral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp
  ring

theorem detector_integrable (χ : AngularCharacter) (hχ : (χ.k ≠ 0 ∨ χ.residue ≠ 1))
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) {x : ℝ} (hx : x ∈ Icc (-(1/4)) 2) (hx0 : x ≠ 0) :
    Integrable (fun t : ℝ => detectorIntegrand χ V D Y ρ ((x : ℂ)+t*I)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth χ.k.natAbs
  let f : ℂ → ℂ := fun z => LFunction χ (ρ+z)
  let g : ℂ → ℂ := fun z => cutoff χ V D (ρ+z)
  have hf : Differentiable ℂ f :=
    (PhysicalAnalytic.nonprincipal_entire χ hχ).comp (differentiable_const ρ |>.add differentiable_id)
  have hg : Differentiable ℂ g :=
    (cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id)
  have hf0 : f 0 = 0 := by simpa [f] using hzero
  obtain ⟨B,_,hb⟩ := cancelledKernel_strip_bound (b := 2) hf hg hf0 hY
    (by norm_num : (-1 : ℝ) < -(1/4)) 2
    (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ (le_refl _) hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith))
  have hi := cancelledKernel_vertical_integrable hf hg (by linarith : 0 < Y)
    (by norm_num : (-1 : ℝ) < -(1/4)) hx hb
  apply hi.congr
  filter_upwards [] with t
  apply cancelledKernel_eq_literal hf0
  intro hz
  apply hx0
  simpa using congrArg Complex.re hz

theorem detectorIntegral_contour_normalization (χ : AngularCharacter) (V : ℝ → ℂ)
    (D Y : ℝ) (ρ : ℂ) :
    detectorIntegral χ V D Y ρ = ((2*Real.pi : ℂ)*I)⁻¹ *
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)*I := by
  rw [MeasureTheory.integral_mul_const, mul_inv_rev]
  simp only [detectorIntegral, ofReal_mul, ofReal_ofNat]
  have hi : I⁻¹*I = 1 := inv_mul_cancel₀ I_ne_zero
  calc
    _ = (I⁻¹*I)*(((2*Real.pi : ℂ))⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) := by rw [hi, one_mul]
    _ = _ := by ring

theorem detector_power_bound (angularOrder : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R θ : ℝ), 0 ≤ R → 0 ≤ θ →
      ∀ (χ : AngularCharacter), χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (U D : ℝ), 1 ≤ U →
      1 ≤ D → D ≤ U^(3/2 : ℝ) → (χ.modulus.absNorm : ℝ) ≤ R*U →
      ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ ≤ (K*R^2)*U^(-(3/2 : ℝ)+2*θ) := by
  obtain ⟨K,hK,hbound⟩ := detector_integral_bound angularOrder
  refine ⟨16*K, by positivity, ?_⟩
  intro R θ hR hθ χ horder hχ V hV U D hU hD hDU hQ ρ hρ hzero ht
  have hU0 : 0 < U := by linarith
  have huθ : 1 ≤ U^θ := Real.one_le_rpow hU hθ
  have hheight : 3+|ρ.im| ≤ 4*U^θ := by linarith
  have hY : 1 ≤ U^20 := one_le_pow₀ hU
  have he : (U^20)^(-(1/4 : ℝ)) = U^(-5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hb := hbound χ horder hχ V hV D (U^20) hD hY ρ hρ hzero
  rw [he] at hb
  calc
    _ ≤ K*(R*U)^2*(4*U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ) := by
      apply hb.trans; gcongr
    _ = (16*K*R^2)*(U^(2 : ℝ)*(U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ)) := by
      rw [Real.rpow_two]; ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hU0.le, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 2
      ring

theorem detector_uniform_small (angularOrder : ℕ) (R θ ε : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : AngularCharacter), χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ D : ℝ, 1 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ < ε := by
  obtain ⟨K,hK,hbound⟩ := detector_power_bound angularOrder
  have ht : Tendsto (fun U : ℝ => (K*R^2)*U^(-(3/2 : ℝ)+2*θ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (3/2 : ℝ)-2*θ)).const_mul (K*R^2)
    simpa [neg_sub, sub_eq_add_neg, add_comm] using h
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ horder hχ V hV D hD hDU hQ ρ hρ hzero ht
  exact (hbound R θ hR hθ χ horder hχ V hV U D hU hD hDU hQ ρ hρ hzero ht).trans_lt (hU₀ U hU₀')

end OAI.SevenEighths.Angular.PhysicalGammaDetector



#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.original_right_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.original_right_growth

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.shifted_original_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.shifted_original_growth

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_contour_shift
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_contour_shift

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_integral_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_integral_bound

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_integrable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_integrable

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.detectorIntegral_contour_normalization
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.detectorIntegral_contour_normalization

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_power_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_power_bound

#print axioms OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_uniform_small
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalGammaDetector.detector_uniform_small
