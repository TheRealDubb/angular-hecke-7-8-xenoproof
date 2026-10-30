import AngularPhysicalPositiveNormalized

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.AllocatedNatural
open PlainRows NaturalRows Dyadic CommonMask
open CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentDivisorRaw
open CenteredMomentCommonMaskEnergy (heightCoefficient heightCoefficient_norm)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos raw_same_product)
local notation "O" => ActualEisensteinCubic.O
theorem original_retained_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : AngularCharacter} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr₁ : 1≤X₁*b₁) (hr₂ : 1≤X₂*b₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      (((clippedScale X₁):ℂ)^(Complex.I*t)*((clippedScale X₂):ℂ)^(Complex.I*t))*
        (Dyadic.polynomial (excluded F.character R) false
          (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ X₁ hX₁ hr₁ t) (clippedScale X₁) 0 0 *
         Dyadic.polynomial (excluded F.character R) false
          (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ X₂ hX₂ hr₂ t) (clippedScale X₂) 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  exact original_positive_normalized F R hR (dilated W₁ (clipDilation X₁))
    (dilated W₂ (clipDilation X₂)) (a₁/max 1 b₁) b₁ (a₂/max 1 b₂) b₂
    (div_pos ha₁ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W₁ a₁ b₁ (max 1 b₁) (clipDilation X₁) ha₁ (le_max_left _ _)
      (clipDilation_ge_one X₁ hX₁) (clipDilation_le b₁ X₁ hX₁ hr₁) hs₁)
    (dilated_support W₂ a₂ b₂ (max 1 b₂) (clipDilation X₂) ha₂ (le_max_left _ _)
      (clipDilation_ge_one X₂ hX₂) (clipDilation_le b₂ X₂ hX₂ hr₂) hs₂)
    (dilated_contDiff W₁ hW₁ _) (dilated_contDiff W₂ hW₂ _) pool β P hP t
    _ _ (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)

theorem original_retained_zero {α : Type*} [Fintype α]
    (η : AngularCharacter) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hz : X₁*b₁<1 ∨ X₂*b₂<1) :
    retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂=0 := by
  unfold retainedPositiveRow positiveSlotRow
  rw [←clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  rcases hz with h|h
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h]
    simp
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h]
    simp

end OAI.SevenEighths.Angular.AllocatedNatural

#print axioms OAI.SevenEighths.Angular.AllocatedNatural.original_retained_normalized
#print axioms OAI.SevenEighths.Angular.AllocatedNatural.original_retained_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AllocatedNatural.original_retained_zero
