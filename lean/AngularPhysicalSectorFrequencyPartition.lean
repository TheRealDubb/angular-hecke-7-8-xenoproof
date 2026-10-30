import AngularPhysicalSectorFrequencySupport
import OAI.NumberTheory.DirichletL.Moments.SecondSectorRetained

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSupport CenteredMomentSecondLedger
open CenteredMomentCanonicalFirst CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization
open CenteredMomentSectorLocalization CenteredMomentSourceRow
open CenteredMomentSecondSectorRetained (physicalKernel)
open PlainRows (heightCoeff)
local notation "O" => ActualEisensteinCubic.O
theorem sectorFrequency_tsum_common (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) :
    (∑' j : O,sectorFrequency η t S β C D hC hD F j)=
      ∑' w : O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) := by
  apply Eq.symm
  refine (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)).tsum_eq
    (f := sectorFrequency η t S β C D hC hD F) ?_
  intro j hj
  obtain ⟨w,hw⟩ := sectorFrequency_common_support η t S β C D hC hD hCD F j hj
  exact ⟨w,hw.symm⟩

theorem sectorFrequency_tsum_partition (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ)
    (hs : Summable (fun w : O=>sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))) :
    (∑' w : O,sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w))=
      ∑ U : Finset (CommonIndex C D),∑' w : O,if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
  have he (w : O) : sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w)=
      ∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := by
    simp [canonicalPartition,eq_comm]
  calc
    _ = ∑' w : O,∑ U : Finset (CommonIndex C D),if canonicalPartition C D U w then
        sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0 := tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun U _=>hs.indicator {w | canonicalPartition C D U w})

theorem sectorFrequency_partition_nonunit (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (F : O→Ideal O→Ideal O→ℂ) :
    (∑' w : O,if canonicalPartition C D U w then
      sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0)=
      ∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD F
          ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  let f : O→ℂ := fun w=>if canonicalPartition C D U w then
    sectorFrequency η t S β C D hC hD F (commonFrequencyGenerator C D*w) else 0
  have hs : Function.support f⊆Set.range (fun h=>nonunitFrequencyGenerator C D U*h) := by
    intro w hw
    have hp : canonicalPartition C D U w := by
      by_contra hn
      exact hw (by simp only [f,ite_eq_right hn])
    obtain ⟨h,hh⟩ := nonunitFrequencyGenerator_dvd C D hC U w hp
    exact ⟨h,hh.symm⟩
  have he := (mul_right_injective₀ (nonunitFrequencyGenerator_ne_zero C D hC U)).tsum_eq hs
  simpa only [f,mul_assoc] using he.symm

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_tsum_common
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_tsum_common

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_tsum_partition
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_tsum_partition

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_partition_nonunit
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_partition_nonunit
