import AngularPhysicalActivePhysicalPartition

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.SecondSource
open PhysicalBlock CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorRetained (physicalKernel)
open CenteredMomentSecondSourceRetained (retainedKernel)
open CenteredMomentSecondRetainedAggregate (commonLabels_supported)
open CenteredMomentSecondRetainedRows (retainedRows retained_mem_rows)
open CenteredMomentActiveSource (activeSource supportedColumns_active)
open CenteredMomentSecondActiveDyadic
  (sourceLower sourceUpper dyadicKernel active_sector_norm sourceLower_pos)
open CenteredMomentSecondDyadicPartition CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSecondBlockAggregate (ActiveLabel SourceBlocks retainedRows_ne_zero)
local notation "O" => ActualEisensteinCubic.O
theorem sector_finite_blocks (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t (activeSource S β) β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑n : SourceBlocks C D U K R H,
        physicalBlock η t (activeSource S β) β C D hC hD U R (retainedRows R A) W K
          (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*h)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [active_kernel_windows η S β H hH C D hC hD I J _ h hA
      (retainedRows_ne_zero R _ h hh) W K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

theorem original_secondRetainedEnergy_blocks (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p : ActiveLabel S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (retainedRows (frequencyRadius Tsec Z ξ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              W K (fun i=>(n i:ℤ)) := by
  rw [←secondRetainedEnergy_active η t S β W K Tsec Z ξ,
    original_retained_energy_GV η t (activeSource S β) β W K Tsec Z ξ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact sector_finite_blocks η t S β H hH _ _ _ _ U W K _ hK

lemma common_height_norm_le_one (η : AngularCharacter) (t : ℝ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) :
    ‖heightCoeff η t C*star (heightCoeff η t D)‖≤1 := by
  rw [norm_mul,norm_star]
  have hc := heightCoeff_norm_le_one η t C hC
  have hd := heightCoeff_norm_le_one η t D hD
  nlinarith [norm_nonneg (heightCoeff η t C),norm_nonneg (heightCoeff η t D)]

theorem original_secondRetainedEnergy_norm_le (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    ‖secondRetainedEnergy η t S β W K Tsec Z ξ‖≤
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
            W K (fun i=>(n i:ℤ))‖ := by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.sector_finite_blocks
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.sector_finite_blocks

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.original_secondRetainedEnergy_blocks
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.original_secondRetainedEnergy_blocks

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.common_height_norm_le_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.common_height_norm_le_one

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.original_secondRetainedEnergy_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.original_secondRetainedEnergy_norm_le
