import AngularPhysicalDetectorSlots
import AngularPhysicalRowAbsolute

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.DetectorSource
open PlainRows ExceptionalRows AngularRowClosure ConcretePrimeRowBridge
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentCounting CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots (whole_product_normalization)
local notation "O" => ActualEisensteinCubic.O
theorem detector_capped_rectangle_uniform (angularType : ℤ) (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : AngularCharacter,η.k=angularType → ∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,hJ⟩:=detector_row_rectangle_uniform angularType ε B hε hB
  obtain ⟨A0,hA0,habs⟩:=detectorSchwartz_absolute
  let D : ℝ:=2*(128*(9/4)*A0)*(128*(9/4)*A0)
  have hD : 0≤D:=by dsimp [D];positivity
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcancel⟩:=hJ Q hQ
  refine ⟨C+D,by positivity,?_⟩
  intro Z hZ η htype m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : 0≤Z^ε:=Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    exact (hcancel Z hZ η htype m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
      t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hpow) (by positivity))
        (div_nonneg (Real.sqrt_nonneg _) hL.le))
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have ha:=normalized_rectangle_absolute η m A z
      (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂)
      (9/4) (9/4) A0 A0 (by norm_num) (by norm_num) hA0.le hA0.le
      (fun x hx=>(detectorSchwartz_support r₁ j σ₁ t₁ hx).2)
      (fun x hx=>(detectorSchwartz_support r₂ k σ₂ t₂ hx).2)
      (habs r₁ j hj σ₁ hσ₁ t₁) (habs r₂ k hk σ₂ hσ₂ t₂)
      h X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    calc
      D≤C+D:=le_add_of_nonneg_left hC.le
      _≤(C+D)*Z^ε:=le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
      _≤(C+D)*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J:=le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by linarith [norm_nonneg t₁,norm_nonneg t₂,norm_nonneg h]))

end OAI.SevenEighths.Angular.DetectorSource

#print axioms OAI.SevenEighths.Angular.DetectorSource.detector_capped_rectangle_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.detector_capped_rectangle_uniform
