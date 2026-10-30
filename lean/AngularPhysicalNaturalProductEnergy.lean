import AngularPhysicalPositiveNormalized
import AngularPhysicalNaturalUnitMask
import AngularPhysicalPlainInductionEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.EnergyAllocatedChildren
open PlainRows NaturalRows CommonMask AllocatedNatural
open OAI.SevenEighths.Angular.Dyadic
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentCommonMaskEnergy (heightCoefficient)
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]
lemma natural_product_eq_positive {η:AngularCharacter}{z:O}(F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i)=
      PlainRows.positiveSlotRow η
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 z
        W₁ W₂ pool β P 0 X₁ X₂:=by
  rw [F.masked_positive 1 one_ne_zero,
    plain_zero_height_ideal _ _ X₁ hX₁,plain_zero_height_ideal _ _ X₂ hX₂]
  simp only [PlainRows.twistedIdealSum,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,
    mul_one,excluded_one_ideal]
  have hn:(Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i:α):(∑I∈pool i,β i I*F.character.idealHom I)=
      ∑I∈pool i,F.character.idealHom I*β i I := by
    apply Finset.sum_congr rfl
    intro I hI
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  simp only [PlainRows.idealSum,div_eq_mul_inv]
  ring

end OAI.SevenEighths.Angular.EnergyAllocatedChildren

#print axioms OAI.SevenEighths.Angular.EnergyAllocatedChildren.natural_product_eq_positive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyAllocatedChildren.natural_product_eq_positive
