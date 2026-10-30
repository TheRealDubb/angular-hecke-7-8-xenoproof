import AngularPhysicalNaturalRowDictionary
import AngularPhysicalCommonMaskRadial
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource

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

lemma plain_zero_height_ideal (χ:AngularCharacter)(W:ℝ→ℂ)(X:ℝ)(hX:0<X) :
    polynomial χ false W X 0 0=(Real.sqrt X:ℂ)⁻¹*idealSum χ W X := by
  simpa only [PlainRows.twistedIdealSum,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,PlainRows.idealSum]
    using PlainRows.plain_zero_height χ W X hX

lemma normalized_twisted_plain (χ : AngularCharacter) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X=
      (X:ℂ)^(Complex.I*t)*Dyadic.polynomial χ false
        (normPowerProfile W a b ha hs hW t) X 0 0 := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,plain_zero_height_ideal _ _ X hX]
  ring

theorem original_positive_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : AngularCharacter} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        (Dyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) X₁ 0 0 *
         Dyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₂ 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  rw [F.masked_positive R hR,twistedIdealSum_scale _ W₁ a₁ b₁ ha₁ hs₁ hW₁ t X₁ hX₁,
    twistedIdealSum_scale _ W₂ a₂ b₂ ha₂ hs₂ hW₂ t X₂ hX₂,
    plain_zero_height_ideal _ _ X₁ hX₁,plain_zero_height_ideal _ _ X₂ hX₂]
  have hn : (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i : α) : (∑I∈pool i,β i I*(excluded F.character R).idealHom I*(I.absNorm:ℂ)^(Complex.I*t))=
      ∑I∈pool i,(excluded F.character R).idealHom I*heightCoefficient (β i) t I := by
    apply Finset.sum_congr rfl
    intro I hI
    unfold heightCoefficient
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  ring

end OAI.SevenEighths.Angular.AllocatedNatural

#print axioms OAI.SevenEighths.Angular.AllocatedNatural.original_positive_normalized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AllocatedNatural.original_positive_normalized
