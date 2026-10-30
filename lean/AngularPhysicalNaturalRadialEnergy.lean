import AngularPhysicalNaturalProductEnergy
import AngularPhysicalNaturalCharacter

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
lemma natural_radial_eq_energy (η:AngularCharacter)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    InductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂ pool β P
      X₁ X₂ r.keep r.profile r.scale:=by
  unfold radialEnergy InductionEnergy.energy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk,naturalCharacter_eq η z (hz z hk)]
    rw [natural_product_eq_positive (naturalRow η z (hz z hk)) W₁ W₂ pool β P X₁ X₂ hX₁ hX₂ hP]
  · simp only [ite_eq_right hk]

omit [Fintype α] in
lemma natural_subset_radial_eq_energy (η:AngularCharacter)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (F:Finset α)(W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    InductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ r.keep r.profile r.scale:=by
  have hh:=natural_radial_eq_energy (α:=F) η r hz W₁ W₂
    (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ hX₁ hX₂
    (fun i=>hP i i.property)
  have hp (z:O):(∏i:F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))=
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i):=
    Finset.prod_coe_sort F (fun i:α=>naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
  simp_rw [hp] at hh
  exact hh

end OAI.SevenEighths.Angular.EnergyAllocatedChildren

#print axioms OAI.SevenEighths.Angular.EnergyAllocatedChildren.natural_radial_eq_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyAllocatedChildren.natural_radial_eq_energy

#print axioms OAI.SevenEighths.Angular.EnergyAllocatedChildren.natural_subset_radial_eq_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyAllocatedChildren.natural_subset_radial_eq_energy
