import AngularPhysicalFirstCommonPower

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
local instance angularFirstCommonSourcePowerReferenceDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem common_energy_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:AngularCharacter)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K Z allowance:ℝ),0<K→0<Z→
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(volume (child s C R B τ t))^(α j))*(∏i,(child s C R B τ t).M i)^2)→
    (commonEnergy (original s R seed) C hC τ t L W K).re≤
      ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
        (Cb*(∏i,s.M i)^2*∑j,normalizedPower b (volume s) (C.absNorm:ℝ)
          (τ.modulus.absNorm:ℝ) Z allowance ε (E j) N (α j)):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_power_budget N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L W K Z allowance hK hZ hW n E α hE hα hchild
  have hV:=volume_pos s
  have hNC:=CenteredMomentFirstScale.norm_pos C hC.1
  have hq:=CenteredMomentFirstScale.norm_pos τ.modulus τ.modulus_ne_bot
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hh':=(div_le_iff₀ hV).mp hh
  apply hh'.trans_eq
  calc
    _ = Cb*(∏i,s.M i)^2*∑j,(C.absNorm:ℝ)^(ε-1)*volume s*E j*
        (b^N*volume s/(C.absNorm:ℝ))^(α j):=by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Cb*(∏i,s.M i)^2*∑j,
        ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
          normalizedPower b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
            Z allowance ε (E j) N (α j):=by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (reference_power_identity b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
        Z allowance ε (E j) N (α j) (zero_lt_one.trans_le hb) hV hNC hq hZ).symm
    _ = _:=by rw [←Finset.mul_sum];ring


end OAI.SevenEighths.Angular.FirstCommonSourcePower

#print axioms OAI.SevenEighths.Angular.FirstCommonSourcePower.common_energy_reference_powers
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstCommonSourcePower.common_energy_reference_powers
