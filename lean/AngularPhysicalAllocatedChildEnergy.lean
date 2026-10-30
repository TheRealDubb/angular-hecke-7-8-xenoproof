import AngularPhysicalNaturalRadialEnergy
import AngularPhysicalAllocatedRadialChildren

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
open PlainRows.CommonRows AllocatedRadial

def allocatedEnergy (η:AngularCharacter)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α):ℝ:=
  InductionEnergy.energy (ι := ↥(liveIndices D a\J)) η
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)) 1 0
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    (fun i:↥(liveIndices D a\J)=>pool i) (fun i:↥(liveIndices D a\J)=>heightCoefficient (β i) t)
    (fun i:↥(liveIndices D a\J)=>P i)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    r.keep r.profile r.scale

lemma child_radial_eq_energy (η:AngularCharacter)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α)
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>child (α:=α) (naturalCharacter η z) D a V₁ V₂ pool β P
      t X₁ X₂ hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale=
      allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J:=by
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  exact natural_subset_radial_eq_energy η r hz (liveIndices D a\J)
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    pool (fun i=>heightCoefficient (β i) t) P
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂) (fun i _=>hP i)

def commonAllocatedEnergy (s:Input α)(τ:AngularCharacter)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)):ℝ:=
  let d:=commonData (withHeight s τ v) C R B
  if left then allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma commonChild_energy (s:Input α)(τ:AngularCharacter)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(hz:∀z,r.keep z→z≠0)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>commonChild s τ v C R B D a V₁ V₂ left z D₁ D₂ J)
      r.keep r.profile r.scale=commonAllocatedEnergy s τ v C R B D a V₁ V₂ r left D₁ D₂ J:=by
  let d:=commonData (withHeight s τ v) C R B
  cases left
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J hD₁ hD₂
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J hD₁ hD₂

end OAI.SevenEighths.Angular.EnergyAllocatedChildren

#print axioms OAI.SevenEighths.Angular.EnergyAllocatedChildren.child_radial_eq_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyAllocatedChildren.child_radial_eq_energy

#print axioms OAI.SevenEighths.Angular.EnergyAllocatedChildren.commonChild_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyAllocatedChildren.commonChild_energy
