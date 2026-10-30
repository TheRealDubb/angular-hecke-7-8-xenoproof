import AngularPhysicalFirstFixedEnergy
import AngularPhysicalFirstAllocationEnergy
import AngularPhysicalFirstMaskedInput

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open CanonicalQuadraticSieve CenteredMomentSourceRow ConcretePrimeRowBridge CommonRows ChildInputs
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentGaussEnergy CenteredMomentAddedZeroUniform
open CenteredMomentFirstPhysicalSource (allocatedData allocated_pools allocated_profile)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance angularFirstAllocatedInputDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

lemma commonEnergy_real (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (commonEnergy D C hC τ t L W K).re =
      AllocationEnergy.commonEnergy D C hC τ t L W K := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).tsum_eq.symm

lemma original_rawVolume (s : Input ι) (R seed : Ideal O) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,volume]

lemma allocated_input_columns (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := by
  have hh := child_columns s C R L B τ t
  simpa only [OriginalData.columns,OriginalData.beta,allocated_pools,allocated_profile,original] using hh

lemma allocated_input_volume (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    AllocationEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold AllocationEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl

theorem common_energy_allocated_inputs (N : ℕ) (a b : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (haS : a≤s.lower) (hbS : s.upper≤b)
    (C R seed : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
      (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑B : actualAllocations s.pools C,
          (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
            childNormalizedGaussSource s C R L B τ t W K := by
  have hh := AllocationEnergy.normalized_common_energy_bound N a b ha
    (original s R seed) hcard s.pools_ne s.prime C hC hseed τ t L W K hK hW
    s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos s.M
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.ν_bound s.W_bound
    (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
  rw [← commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
    (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
      ∑B : actualAllocations s.pools C,
        (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
          (AllocationEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
            CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)) at hh
  simpa only [allocated_input_energy] using hh

lemma allocated_input_masked_energy (s : Input ι) (C R T seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    AllocationEnergy.allocatedEnergy (original s (R*T) seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s (R*T) seed) C L B)=
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) L).columns
      (CenteredMomentFirstMaskedFamily.maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) L).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) := by
  rw [allocated_input_energy,MaskedInput.normalized_child_mask]

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.commonEnergy_real
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.commonEnergy_real

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_rawVolume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.original_rawVolume

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_columns
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_columns

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_volume

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_energy

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.common_energy_allocated_inputs
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.common_energy_allocated_inputs

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_masked_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.allocated_input_masked_energy
