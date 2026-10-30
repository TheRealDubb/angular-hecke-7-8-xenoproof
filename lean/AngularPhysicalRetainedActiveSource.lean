import AngularPhysicalRetainedFiniteRows

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
theorem secondRetainedEnergy_eq_sum (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K T Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*heightCoeff η t I)*
          star (β J*heightCoeff η t J))*
          retainedKernel I J W K T Z ξ := by
  unfold secondRetainedEnergy
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel,dite_eq_left (Finset.mem_filter.mp I.property).2,
    dite_eq_left (Finset.mem_filter.mp J.property).2]

theorem secondRetainedEnergy_active (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t (activeSource S β) β W K T Z ξ=
      secondRetainedEnergy η t S β W K T Z ξ := by
  rw [secondRetainedEnergy_eq_sum,secondRetainedEnergy_eq_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : β J=0 <;> simp [hj]

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.secondRetainedEnergy_eq_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.secondRetainedEnergy_eq_sum

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.secondRetainedEnergy_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.secondRetainedEnergy_active
