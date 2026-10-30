import AngularPhysicalPlainHeight
import OAI.NumberTheory.DirichletL.Hecke.UnitRows

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalUnitEuler
open CenteredMomentRowNorm HeckeFamily
local notation "O" => ActualEisensteinCubic.O

def reflected (η:AngularCharacter):AngularCharacter:=AngularRowClosure.finiteTwist η (HeckeUnitRows.character (-1:Oˣ))

theorem unit_ideal (I:Ideal O)(hI:Supported I):
    idealCoeff (HeckeUnitRows.character (-1:Oˣ)) I=idealRowHom (-1) I:=by
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,
    idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {ConcretePrimeRowBridge.idealGenerator I}) then _ else 0)=_
  rw [ConcretePrimeRowBridge.span_idealGenerator,ite_eq_left hI]
  rfl

theorem reflected_height (η:AngularCharacter)(t:ℝ)(I:Ideal O)(hI:Supported I):
    heightCoeff (reflected η) t I=heightCoeff η t I*idealRowHom (-1) I:=by
  rw [heightCoeff,reflected,ExceptionalRows.finiteTwist_idealHom,unit_ideal I hI,heightCoeff]
  ring

theorem polynomial_neg {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(η:AngularCharacter)(t:ℝ)(z:O):
    rowPolynomial S a (fun i=>c i*heightCoeff η t (Ideal.span {a i})) (-z)=
      rowPolynomial S a (fun i=>c i*heightCoeff (reflected η) t (Ideal.span {a i})) z:=by
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [reflected_height η t _ (ha i),show -z=(-1)*z by ring,idealRowHom_argument_mul]
  ring

theorem reflected_row (η:AngularCharacter)(m A z n:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    rowTwist η.elementHom.toMonoidHom m 1 (A*(-z)) n=
      rowTwist (reflected η).elementHom.toMonoidHom m 1 (A*z) n:=by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 _ n hn,rowTwist_extract_sixth_mask _ m 1 _ n hn]
    simp only [one_pow,one_mul]
    change η.elementCoeff n*coprimalityMask m n*idealRowHom (A*(-z)) (Ideal.span {n})=
      (reflected η).elementCoeff n*coprimalityMask m n*idealRowHom (A*z) (Ideal.span {n})
    rw [reflected,AngularRowClosure.elementCoeff_finiteTwist,HeckeUnitRows.elementCoeff_character]
    have hu:unitSupplement (-1:Oˣ) n=idealRowHom (-1) (Ideal.span {n}):=by
      change (if Supported (Ideal.span {n}) then idealRowHom (-1) (Ideal.span {n}) else 0)=_
      rw [ite_eq_left hn]
    rw [hu,show A*(-z)=(-1)*(A*z) by ring,idealRowHom_argument_mul]
    ring
  · rw [CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn]

theorem reflected_inducing (η:AngularCharacter)(Q:Ideal O)(m A z:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    ExceptionalRows.FixedInducingRow η Q m A (-z) ↔
      ExceptionalRows.FixedInducingRow (reflected η) Q m A z:=by
  unfold ExceptionalRows.FixedInducingRow
  simp_rw [←reflected_row η m A z _ hmLam hm2]
  rfl


theorem reflected_k (η : AngularCharacter) : (reflected η).k=η.k := rfl

end OAI.SevenEighths.Angular.PlainRows

namespace OAI.SevenEighths.Angular.ExceptionalRows
open ChildRows RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def nonexceptional (η : AngularCharacter) (χ : RayCharacter) (Q : Ideal O) (m A z : O) : Prop :=
  z≠0 ∧ ¬FixedInducingRow (childCharacter η χ) Q m A z

theorem nonexceptional_reflection (η : AngularCharacter) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m A z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m) :
    nonexceptional η χ Q m A z ↔ nonexceptional η ξ Q m A (-z) := by
  unfold nonexceptional
  rw [neg_ne_zero]
  exact and_congr Iff.rfl (not_fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

theorem nonexceptional_ray_independent (η : AngularCharacter) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q≤Ideal.span {(72:O)}) (m A z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m) :
    nonexceptional η χ Q m A z ↔ nonexceptional η ξ Q m A z := by
  have h₁ := nonexceptional_reflection η χ ξ Q hQ m A z hmLam hm2
  have h₂ := nonexceptional_reflection η ξ ξ Q hQ m A (-z) hmLam hm2
  simpa only [neg_neg] using h₁.trans h₂

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.nonexceptional_ray_independent
