import AngularPhysicalFirstCommonBudget

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.FirstCommonSourcePower
open CanonicalQuadraticSieve PlainRows.CommonRows PlainRows.ChildInputs
open PlainRows.FirstPhysical PlainRows.ChildSourceCaps
open PlainRows.FirstPhysical.AllocationEnergy (allocatedEnergy allocated_nonneg normalized_common_energy_allocation)
open CenteredMomentFirstAllocationGaussEnergy (rawVolume frozenControl frozen_normalized_bound)
open CenteredMomentFirstPhysicalSource (allocatedData)
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentFirstCommonReferencePower (normalizedPower reference_power_identity)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance angularFirstCommonSourcePowerPowerDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem common_energy_power_budget (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:AngularCharacter)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ),0<K →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(PlainRows.CommonRows.volume (child s C R B τ t))^(α j))*
          (∏i,(child s C R B τ t).M i)^2)→
    (PlainRows.FirstPhysical.commonEnergy (original s R seed) C hC τ t L W K).re/
      PlainRows.CommonRows.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*
          (∑j,E j*(b^N*PlainRows.CommonRows.volume s/(C.absNorm:ℝ))^(α j))*
            (∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound,hCbound,?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hv:=PlainRows.CommonRows.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  apply hbound s hcard haS hbS C R seed hC hseed τ t L W K _ hK
    (Finset.sum_nonneg (fun j _=>mul_nonneg (hE j) (Real.rpow_nonneg (by positivity) _))) hW
  intro B hB
  apply (hchild B hB).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hE j)
  exact Real.rpow_le_rpow (PlainRows.CommonRows.volume_pos _).le
    (PlainRows.ChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) (hα j)


end OAI.SevenEighths.Angular.FirstCommonSourcePower

#print axioms OAI.SevenEighths.Angular.FirstCommonSourcePower.common_energy_power_budget
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstCommonSourcePower.common_energy_power_budget
