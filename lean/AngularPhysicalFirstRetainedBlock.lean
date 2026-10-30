import AngularPhysicalFirstRetainedPhysical
import OAI.NumberTheory.DirichletL.Moments.FirstRetainedBlock

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CompletedGauss CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstCommonFourierTransport
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentSectorLocalization CenteredMomentFirstScale
local notation "O"=>ActualEisensteinCubic.O

open CenteredMomentFirstRetainedBlock (retainedFourierTerm_finite finite_pair_row_sum)

theorem fixed_sector_term_block
    (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0)=
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedTerm
  generalize_proofs
  simp_rw [retainedFourierTerm_finite]
  rw [finite_pair_row_sum]
  rw [retainedInfiniteBlock_eq_finite]
  unfold retainedBlock inactiveWeight
  dsimp only
  simp only [normValue_eq_embedding]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> ring

theorem fixed_sector_blocks
    (η:AngularCharacter)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    fixedRetainedSector η m A t S c C D hC hD W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        retainedInfiniteBlock η m A t S c C D hC hD E W K
          (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedSector
  apply Finset.sum_congr rfl
  intro E hE
  exact fixed_sector_term_block η m A t S c C D hC hD E W K X Z ξ

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.fixed_sector_term_block
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.fixed_sector_term_block

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.fixed_sector_blocks
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.fixed_sector_blocks
