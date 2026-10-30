import AngularPhysicalSecondLiveBlocks
import AngularPhysicalSecondPartRows

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
def partEnergy (exceptional:Bool)(η:AngularCharacter)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):ℂ:=
  ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))

theorem original_energy_split (η:AngularCharacter)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ)(hK:0<K)
    (hH:∀I∈S,β I≠0→(I.absNorm:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      partEnergy true η χ Q m t S β W K Tsec Z ξ H+
      partEnergy false η χ Q m t S β W K Tsec Z ξ H:=by
  rw [original_live_blocks η t S β W K Tsec Z ξ H hK hH]
  unfold partEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [partRows_false]
  exact physicalBlock_filter_split η t (activeSource S β) β p.val.1 p.val.2 _ _ U
    (frequencyRadius Tsec Z ξ) (sourceRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)) W K _ _

theorem partEnergy_norm_le (exceptional:Bool)(η:AngularCharacter)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖≤
  ∑p∈liveLabels η S β,
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))‖
 :=by
  unfold partEnergy
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

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.original_energy_split
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.original_energy_split

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.partEnergy_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.partEnergy_norm_le
