import AngularPhysicalPlainHeight
import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentSecondDivisorSupport (live_right_divisor_norm)
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
theorem right_divisor_coefficient_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:AngularCharacter)(t:ℝ)(A:O)(ξ:RayCharacter)(I:sectorPool D hD.1 S):
    divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient A (sectorElement D hD.1 S)
        (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I=0:=by
  unfold divisorCoefficient
  rw [sectorElement_span]
  split_ifs with hd
  · have hz:β (D*I)=0:=by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (sectorPool_supported D hD.1 S I).1 β H hβ hn hd)
    simp only [movingCoefficient,hz,zero_mul]
  · rfl

theorem right_divisor_row_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:AngularCharacter)(t:ℝ)(A:O)(ξ:RayCharacter)(v:sectorPool D hD.1 S→ℂ)(z:O):
    rowPolynomial Finset.univ (sectorElement D hD.1 S)
      (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
        (movingCoefficient A (sectorElement D hD.1 S)
          (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v I) z=0:=by
  unfold rowPolynomial
  apply Finset.sum_eq_zero
  intro I hI
  exact mul_eq_zero_of_left
    (mul_eq_zero_of_left (right_divisor_coefficient_zero D hD S β H hβ L hL η t A ξ I) _) _

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.right_divisor_coefficient_zero
#print axioms OAI.SevenEighths.Angular.PlainRows.right_divisor_row_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.right_divisor_row_zero
