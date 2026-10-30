import AngularPhysicalRetainedSourceAggregate
import AngularPhysicalSecondBlock
import OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate

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
theorem physical_sector_zero_of_weight (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (j : O)
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem physical_partition_finite_rows (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A : O) (hA : A≠0) (part : O→Prop) :
    (∑' h : O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  intro h hh
  by_cases hp : part h
  · rw [ite_eq_left hp]
    apply physical_sector_zero_of_weight η t S β C D hC hD W K R (A*h)
    by_contra hn
    exact hh (retained_mem_rows R A h hA hn)
  · rw [ite_eq_right hp]

theorem actual_GV_finite_rows (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.physical_sector_zero_of_weight
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.physical_sector_zero_of_weight

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.physical_partition_finite_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.physical_partition_finite_rows

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.actual_GV_finite_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.actual_GV_finite_rows
