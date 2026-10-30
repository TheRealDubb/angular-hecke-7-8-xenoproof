import AngularPhysicalSecondLiveLabels

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

open ChildRows RayFourExpansion
open ExceptionalRows (nonexceptional)
open CenteredMomentSecondLiveBlock (liveRows liveRows_weight liveRows_geometry)
open CenteredMomentSecondEnergySplit (sourceRows sourceRows_nonzero)
lemma physicalBlock_live_rows (η:AngularCharacter) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

lemma physicalBlock_row_split (η:AngularCharacter) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ) (p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter p) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬p z)) W K n:=by
  rw [physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not _ p _).symm

theorem original_live_blocks (η:AngularCharacter) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H:ℝ) (hK:0<K)
    (hH:∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (liveRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)
                (retainedRows (frequencyRadius Tsec Z ξ)
                  (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)))
              W K (fun i=>(n i:ℤ)):=by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  trans ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
          W K (fun i=>(n i:ℤ))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hn
    rw [common_height_zero_of_not_live η t S β p hn,zero_mul]
  · apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun x : ℂ => heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) * x)
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_live_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.physicalBlock_live_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.physicalBlock_live_rows

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.physicalBlock_row_split
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.physicalBlock_row_split

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.original_live_blocks
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.original_live_blocks
