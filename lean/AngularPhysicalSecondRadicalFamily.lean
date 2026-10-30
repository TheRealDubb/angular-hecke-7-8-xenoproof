import AngularPhysicalRadicalPresentation
import OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget

noncomputable section
open scoped Classical BigOperators Topology
namespace OAI.SevenEighths.Angular.SecondFamily
open PlainRows ChildRows AngularRowClosure
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalLedger
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentCanonicalFirst CenteredMomentPartitionNorm CenteredMomentSupport
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentSecondRadicalFamily (active_radical_product)
open CenteredMomentSecondRadicalBudget (fixedFactor fixedFactor_pos active_radical_norm_bound)
local notation "O" => ActualEisensteinCubic.O
theorem exists_second_radical_family (η : AngularCharacter) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : AngularCharacter, τ.k=η.k ∧
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      (∀n:O,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom
        fixedBadMask 1 (reducedNumerator C D U) n) ∧
      ∀I:Ideal O,Supported I → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hk,hM,hN,hτ⟩ := exists_radical_row_presentation (childCharacter η χ) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (activePrime C D U) (fun P=>commonPrime_supported C D hC P.val)
    (activeExponent C D U) (activeExponent_pos C D U)
  have he (n:O) : τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom
      fixedBadMask 1 (reducedNumerator C D U) n := by
    rw [reducedNumerator_active_product]
    exact hτ n
  refine ⟨τ,hk,?_,he,?_⟩
  · rw [←map_prod,active_radical_product C D hC U] at hN
    exact hN
  · intro I hI t
    exact row_presentation_height η τ χ (reducedNumerator C D U) he I hI t

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.exists_second_radical_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.exists_second_radical_family
