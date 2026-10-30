import AngularPhysicalExceptionalProduct

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open ChildRows CenteredMomentFixedRay RayFourExpansion
open CenteredMomentExceptionalPair (rayRatio reflectionRatio reflectionRatio_modulus)
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem child_rows_zero_off_support (η : AngularCharacter) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (childCharacter η χ).elementHom.toMonoidHom m 1 (A*z) n = 0 ∧
      rowTwist (childCharacter η ξ).elementHom.toMonoidHom m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn⟩

theorem child_row_reflection (η : AngularCharacter) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (childCharacter η ξ).elementHom.toMonoidHom m 1 (A*(-z)) n =
      rowTwist (childCharacter η χ).elementHom.toMonoidHom m 1 (A*z) n *
        HeckeFamily.elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*z) n hn]
    simp only [one_pow, one_mul]
    change (childCharacter η ξ).elementCoeff n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      ((childCharacter η χ).elementCoeff n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * HeckeFamily.elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, HeckeFamily.elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if Supported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [ite_eq_left hn]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem child_row_reflection_hom (η : AngularCharacter) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    rowTwist (childCharacter η ξ).elementHom.toMonoidHom m 1 (A*(-z)) =
      rowTwist (childCharacter η χ).elementHom.toMonoidHom m 1 (A*z) *
        HeckeRowClosure.elementHom (reflectionRatio χ ξ) := by
  ext n
  exact child_row_reflection η χ ξ m A z hmLam hm2 n

theorem fixedInducingRow_reflected (η : AngularCharacter) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_finite_product (childCharacter η χ) (childCharacter η ξ) rfl
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : AngularCharacter) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : AngularCharacter) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixedInducingRow_reflection_iff
