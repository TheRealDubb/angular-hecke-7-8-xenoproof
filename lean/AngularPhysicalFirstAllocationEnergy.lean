import AngularPhysicalFirstAllocation
import OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy
open CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy
open CenteredMomentFirstPhysicalSource (allocatedData)
open CenteredMomentFirstAllocationGaussEnergy (rawVolume rawVolume_pos allocated_rawVolume
  rawVolume_both frozenControl frozen_normalized_bound)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance angularFirstAllocationEnergyDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def commonEnergy (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : AngularCharacter) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

lemma common_summable (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).summable

lemma allocated_hasSum (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : AngularCharacter) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O =>
      ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
        (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (allocatedEnergy D C L B τ t W K) :=
  gaussEnergy_hasSum_re _ _ _ _ W K hK

lemma allocated_nonneg (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : AngularCharacter) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤allocatedEnergy D C L B τ t W K := by
  rw [← (allocated_hasSum D C L B τ t W K hK).tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

theorem common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I∈D.S i, I≠0) (hp : ∀ i, ∀ I∈D.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    commonEnergy D C hC τ t L W K ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K := by
  unfold commonEnergy
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows, ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
          (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [common_gauss_allocation D hS hp C hC hseed τ t L z]
      have hc := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B : actualAllocations D.S C =>
            frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
              gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
                (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z))
        (hW z)
      simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hc
    _ = ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          ∑ z∈rows, ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
            (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z))
        (allocated_hasSum D C L B τ t W K hK)

theorem normalized_common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        (‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  have hV := rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP
  have he := div_le_div_of_nonneg_right
    (common_energy_allocation D hS hp C hC hseed τ t L W K hK hW) hV.le
  apply he.trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations D.S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hR := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
  field_simp

theorem normalized_common_energy_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) (M : ι → ℝ) (hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hslot : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      (max 1 b)^N * ((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑ B : actualAllocations D.S C, (frozenControl B.val M)^2 *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  apply (normalized_common_energy_allocation D hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP).trans
  calc
    _ ≤ ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ((max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      have hVa : 0<rawVolume (allocatedData D C L B) := by
        rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
        exact div_pos (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)
          (rawReduction_pos B.val (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP)
      exact mul_le_mul_of_nonneg_right
        (frozen_normalized_bound N a b ha D hcard C hC.1 B M hM hP hν hWnorm hslot)
        (div_nonneg (allocated_nonneg D C L B τ t W K hK hW) hVa.le)
    _ = _ := by
      simp only [mul_assoc,← Finset.mul_sum]
      ring

theorem normalized_common_as_tsum (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hV : 0<rawVolume D) :
    (∑' z : O, ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) =
      commonEnergy D C hC τ t L W K/rawVolume D := by
  have hn (z : O) : ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 =
      ‖commonGauss D C hC τ t L z‖^2/rawVolume D := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow,inv_pow,Real.sq_sqrt hV.le]
    ring
  simp_rw [hn,div_mul_eq_mul_div]
  exact tsum_div_const

theorem allocated_sum_hasSum (D : OriginalData ι) (C L : Ideal O)
    (τ : AngularCharacter) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ∑ B : actualAllocations D.S C,
      ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
        (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re))
      (∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K) := by
  exact hasSum_sum (fun B _ => (allocated_hasSum D C L B τ t W K hK).mul_left _)

theorem original_radial_bound (N : ℕ) (a b : ℝ) (ha : 0<a) :
    ∃ F : ℝ,0<F ∧ ∀ {κ : Type*} [Fintype κ],∀ D : OriginalData κ,
      Fintype.card κ≤N →
      (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
      ∀ (C : Ideal O) (hC : Supported C), D.s∣C →
      ∀ (τ : AngularCharacter) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T : ℝ),
      0<K → (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      0<D.X₁ → 0<D.X₂ → D.B₁≠0 → D.B₂≠0 →
      (∀ i,0<D.lengths i) → D.X₁*D.X₂=T → D.Y₁*D.Y₂=T →
      ∀ M : κ → ℝ,(∀ i,0≤M i) → (∀ i I,‖D.nu i I‖≤1) →
      (∀ i x,‖D.slot i x‖≤M i) →
      (∀ i,Function.support (D.slot i)⊆Set.Icc a b) →
      (∑' z : O,
        ‖(Real.sqrt ((T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i):ℂ)⁻¹ *
          commonGauss D C hC τ t L z‖^2 * (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) ≤
        F*((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          ∑ B : actualAllocations D.S C,(frozenControl B.val M)^2 *
            (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  refine ⟨(max 1 b)^N,pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _,?_⟩
  intro κ _ D hcard hS hp C hC hseed τ t L W K T hK hW hX₁ hX₂ hB₁ hB₂ hP hX hY M hM hν hWnorm hslot
  rw [← (rawVolume_both D T hX hY).1,
    normalized_common_as_tsum D C hC τ t L W K (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)]
  exact normalized_common_energy_bound N a b ha D hcard hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP M hM hν hWnorm hslot

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.common_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.common_summable

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.allocated_hasSum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.allocated_hasSum

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.allocated_nonneg
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.allocated_nonneg

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.common_energy_allocation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.common_energy_allocation

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.normalized_common_energy_allocation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.normalized_common_energy_allocation

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.normalized_common_energy_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.normalized_common_energy_bound

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.normalized_common_as_tsum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.normalized_common_as_tsum

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.allocated_sum_hasSum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.allocated_sum_hasSum

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.original_radial_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.AllocationEnergy.original_radial_bound
