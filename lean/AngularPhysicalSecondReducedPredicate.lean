import AngularPhysicalPlainSecondTransport
import AngularPhysicalSecondRetainedWidth
import AngularPhysicalFixedRowMask
import AngularPhysicalSecondCommonSupport
import AngularPhysicalSecondLiveRows
import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.SecondFamily
open PlainRows ChildRows ExceptionalRows PhysicalBlock
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalLedger
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthSource
open CenteredMomentCanonicalFirst CenteredMomentPartitionNorm CenteredMomentSupport
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentSecondSixthReduction (reducedNumerator sixthFactor fixed_sixth_factorization
  sixthFactor_ne_zero reducedNumerator_ne_zero)
open CenteredMomentSecondRadicalBudget (fixedFactor fixedFactor_pos)
open CenteredMomentSecondRadicalColumns (residual_sixth_coefficient_right)
open CenteredMomentSecondLiveBlock (liveRows liveRows_geometry liveRows_weight)
open CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
theorem fixed_sixth_row (η : AngularCharacter) (m h n : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    rowTwist η.elementHom.toMonoidHom m 1
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) n=
    rowTwist η.elementHom.toMonoidHom (m*sixthFactor C D U) 1 (reducedNumerator C D U*h) n := by
  rw [fixed_sixth_factorization]
  have he : m ^ 6 * 1 ^ 4 * ((reducedNumerator C D U * sixthFactor C D U ^ 6) * h) =
      (m * sixthFactor C D U) ^ 6 * 1 ^ 4 * (reducedNumerator C D U * h) := by ring
  exact congrArg
    (fun x => η.elementCoeff n * idealRowHom x (Ideal.span {n})) he

theorem fixed_sixth_inducing_iff (η : AngularCharacter) (Q : Ideal O) (m h : O)
    (hm : m≠0) (hh : h≠0) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q m (reducedNumerator C D U) h := by
  have he : FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q (m*sixthFactor C D U) (reducedNumerator C D U) h := by
    unfold FixedInducingRow
    simp only [fixed_sixth_row]
  exact he.trans (fixedInducingRow_mul_mask_iff η Q m (sixthFactor C D U)
    (reducedNumerator C D U) h hm (sixthFactor_ne_zero C D hC U)
    (reducedNumerator_ne_zero C D hC U) hh hmLam hm2)

theorem actual_reduced_inducing_iff (η τ : AngularCharacter) (htype:τ.k=η.k) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ htype χ _ hτ Q z).symm

theorem actual_nonexceptional_iff (η τ : AngularCharacter) (htype:τ.k=η.k) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp only [hz,ne_eq,not_true_eq_false,false_and]
  · rw [actual_reduced_inducing_iff η τ htype χ C D hC U hτ Q m z hm hz hmLam hm2]

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.actual_nonexceptional_iff
#print axioms OAI.SevenEighths.Angular.SecondFamily.fixed_sixth_inducing_iff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.fixed_sixth_inducing_iff
