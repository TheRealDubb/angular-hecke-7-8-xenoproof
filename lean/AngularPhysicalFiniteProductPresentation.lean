import AngularPhysicalPlainSecondTransport
import AngularPrimeDeletion
import OAI.NumberTheory.DirichletL.Moments.FirstFamily

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PlainRows
open AngularRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimaryCharacter CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


theorem finiteProduct_le (η : AngularCharacter) (χ : HeckeFamily.Character) :
    η.modulus*χ.modulus ≤ (finiteTwist η χ).modulus := Ideal.mul_le_inf

def finiteProductPresentation (η : AngularCharacter) (χ : HeckeFamily.Character) : AngularCharacter :=
  (finiteTwist η χ).refineModulus (η.modulus*χ.modulus)
    (mul_ne_zero η.modulus_ne_bot χ.modulus_ne_bot) (finiteProduct_le η χ)

theorem finiteProductPresentation_k (η : AngularCharacter) (χ : HeckeFamily.Character) :
    (finiteProductPresentation η χ).k=η.k := rfl

theorem finiteProductPresentation_elementCoeff (η : AngularCharacter) (χ : HeckeFamily.Character) (n : O) :
    (finiteProductPresentation η χ).elementCoeff n=η.elementCoeff n*HeckeFamily.elementCoeff χ n := by
  rw [finiteProductPresentation,AngularCharacter.elementCoeff_refineModulus,elementCoeff_finiteTwist]
  by_cases h : IsUnit (Ideal.Quotient.mk (η.modulus*χ.modulus) n)
  · rw [ite_eq_left h]
  · have hz : η.elementCoeff n*HeckeFamily.elementCoeff χ n=0 := by
      by_contra hn
      have hη := ChildRows.old_coefficient_nonzero_coprime η n (left_ne_zero_of_mul hn)
      have hχ : IsCoprime (Ideal.span {n}) χ.modulus :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
          (MulChar.apply_ne_zero_iff.mp (right_ne_zero_of_mul hn))
      exact h ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr (hη.mul_right hχ))
    rw [ite_eq_right h,hz]

theorem exists_supported_row_presentation (η : AngularCharacter) (m z : O)
    (hm : m≠0) (hz : Supported (Ideal.span {z})) (hmLam : λ₀∣m) (hm2 : (2:O)∣m) :
    ∃ τ : AngularCharacter, τ.k=η.k ∧
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {z} ∧
      ∀ n : O,τ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 z n := by
  obtain ⟨χ,hM,hχ⟩ := CenteredMomentFirstFamily.exists_supported_row_presentation
    finiteTrivial m z hm hz hmLam hm2
  refine ⟨finiteProductPresentation η χ,rfl,?_,?_⟩
  · change η.modulus*χ.modulus=_
    rw [hM]
    change η.modulus*((⊤:Ideal O)*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {z})=_
    simp only [Ideal.top_mul,mul_assoc]
  · intro n
    rw [finiteProductPresentation_elementCoeff,hχ]
    change η.elementCoeff n*(HeckeFamily.elementCoeff finiteTrivial n*
      idealRowHom (m^6*1^4*z) (Ideal.span {n}))=
      η.elementCoeff n*idealRowHom (m^6*1^4*z) (Ideal.span {n})
    rw [finiteTrivial_elementCoeff,one_mul]

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.exists_supported_row_presentation
