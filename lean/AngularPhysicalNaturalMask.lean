import AngularPrimeDeletion
import AngularPhysicalFixedRowMask
import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.NaturalRows
open CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource (support_prime coprime_support_iff fixedConductorFactor)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open ExceptionalRows (FixedInducingRow row_mask_mul fixedInducingRow_mul_mask_iff)
local notation "O" => ActualEisensteinCubic.O

def excluded (χ : AngularCharacter) (R : Ideal O) : AngularCharacter :=
  χ.excludePrimes (primeSupport R) (support_prime R)

theorem excluded_k (χ : AngularCharacter) (R : Ideal O) : (excluded χ R).k=χ.k := rfl

theorem excluded_ideal (χ : AngularCharacter) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    (excluded χ R).idealHom I=if IsCoprime I R then χ.idealHom I else 0 := by
  simp only [excluded,AngularCharacter.idealHom_excludePrimes,coprime_support_iff I R hR]

theorem excluded_element (χ : AngularCharacter) (R : Ideal O) (hR : R≠0) (n : O) :
    (excluded χ R).elementCoeff n=
      if IsCoprime (Ideal.span {n}) R then χ.elementCoeff n else 0 := by
  rw [←AngularCharacter.idealHom_span,excluded_ideal χ R hR,AngularCharacter.idealHom_span]

theorem excluded_element_generator (χ : AngularCharacter) (R : Ideal O) (hR : R≠0) (n : O) :
    (excluded χ R).elementCoeff n=
      if IsCoprime n (idealGenerator R) then χ.elementCoeff n else 0 := by
  rw [excluded_element χ R hR]
  conv_lhs => rw [←span_idealGenerator R,Ideal.isCoprime_span_singleton_iff]


end OAI.SevenEighths.Angular.NaturalRows

#print axioms OAI.SevenEighths.Angular.NaturalRows.excluded_element_generator
