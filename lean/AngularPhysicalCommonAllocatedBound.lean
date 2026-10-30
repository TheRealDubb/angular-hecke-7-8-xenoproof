import AngularPhysicalLiveSourcePaidCapacity
import AngularPhysicalAllocatedCommonEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.CanonicalPaid
open EnergyState EnergyBands RelativePrime InductionEnergy PlainRows
open EnergyAllocatedChildren EnergyPaid PlainRows.CommonRows PlainRows.AllocatedRayDictionary
open AllocatedNatural AllocatedRadial NaturalRows ChildState ConcreteTraceCRT PlainRows.RadialEnergy
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
open CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedClipped (pair scale scale_pos scale_cap)
open CenteredMomentEnergyBands (length)
open CenteredMomentSectorLocalization (dyadicScale dyadicScale_pos)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]

open CenteredMomentNaturalRowSource (support_prime)
theorem actual_common_from_energy (b M:α→ℝ)(hM:∀i,0≤M i)(ε:ℝ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀s:Input α,(∀i,s.hi i≤b i)→(∀i,s.M i≤M i)→
    ∀(τ:AngularCharacter)(v:ℝ)(C R:Ideal O),R≠0→∀B:actualAllocations s.pools C,
    ∀(L:Ideal O)(a:Allocation L (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂:Plain,V₁.W=s.W₁→V₂.W=s.W₂→∀r:Radial,(∀z,r.keep z→z≠0)→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀left:Bool,∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
      ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      commonAllocatedEnergy s τ v C R B L a V₁ V₂ r left D₁ D₂ J≤(if left then E₁ else E₂))→
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂):=by
  obtain ⟨C₀,hC₀,hbound⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂ he
  apply hbound s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz true D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he true D₁ hD₁ D₂ hD₂ J hJ
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz false D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he false D₁ hD₁ D₂ hD₂ J hJ

end OAI.SevenEighths.Angular.CanonicalPaid

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.actual_common_from_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.actual_common_from_energy
