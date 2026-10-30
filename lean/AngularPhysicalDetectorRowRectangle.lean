import AngularPhysicalDetectorRectangle
import AngularPhysicalControlledInducing

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.DetectorSource
open PlainRows ExceptionalRows AngularRowClosure ConcretePrimeRowBridge
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentCounting CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots (whole_product_normalization)
local notation "O" => ActualEisensteinCubic.O
theorem detector_row_rectangle_uniform (angularType : ℤ) (ε B : ℝ) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ∀η : AngularCharacter,η.k=angularType → ∀m A z : O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^B → FixedInducingRow η Q m A z →
      ∀r₁ r₂ : Bool,∀j k : ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h X₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h X₂-
        rowTwistedSum η m A z (detectorSchwartz r₁ j σ₁ t₁) h Y₁*rowTwistedSum η m A z (detectorSchwartz r₂ k σ₂ t₂) h Y₂)‖≤
        C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩:=detector_rectangle_uniform angularType ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro Z hZ η htype m A z hm hA hz hml hm2 hcond hex r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,_,hψk,hχ,hprim,hind,hQψ,hrow⟩:=fixedInducingRow_controlled η Q m A z hm hA hz hml hm2 hex
  have hχnorm : (χ.modulus.absNorm:ℝ)≤Z^B :=
    (show (χ.modulus.absNorm:ℝ)≤rowConductorBound η m 1 (A*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A z hrow]
  exact hbound Z hZ η χ ψ (hψk.trans htype) hχnorm hQψ hind m A z hml hm2 hrow r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ h X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end OAI.SevenEighths.Angular.DetectorSource

#print axioms OAI.SevenEighths.Angular.DetectorSource.detector_row_rectangle_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.detector_row_rectangle_uniform
