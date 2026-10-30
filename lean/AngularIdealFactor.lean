import AngularTotalFourier

noncomputable section
open scoped Classical
namespace OAI.CubicEisenstein.AngularIdealFactor
open SevenEighths SevenEighths.Angular CanonicalCoefficientClass CanonicalRowCompletion
open InverseInitialRayAttachment AngularCanonicalCoefficient AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O

/-- The actual coefficient is an explicit fixed angular factor times a bounded
finite-periodic factor. Periodicity is required only of the latter. -/
def HasNegativeAngularFactor (order q : ℕ) (actual : Eis →* ℂ) : Prop :=
  ∃ finiteBase : Eis →* ℂ, (∀ a, ‖finiteBase a‖ ≤ 1) ∧
    FactorsModulo (fixedBaseConductor q) finiteBase ∧
    actual = negativeAngularTwist finiteBase order

theorem factor_norm_le_one {order q : ℕ} {actual : Eis →* ℂ}
    (h : HasNegativeAngularFactor order q actual) (a : Eis) : ‖actual a‖ ≤ 1 := by
  obtain ⟨base, hb, hp, rfl⟩ := h
  exact negativeAngularTwist_norm_le_one base order hb a

theorem actual_negative_element (χ : AngularCharacter) (order : ℕ)
    (hk : χ.k = -(order : ℤ))
    (hzero : order ≠ 0 ∨ finiteResidueHom χ 0 = 0) :
    χ.elementHom.toMonoidHom = negativeAngularTwist (finiteResidueHom χ) order := by
  ext a
  by_cases ha : a = 0
  · subst a
    change χ.elementCoeff 0 = star (alpha 0) ^ order * finiteResidueHom χ 0
    rcases hzero with hn | hz
    · simp [alpha, FiniteGaussPhase.angularFactor, hn]
    · rw [hz, mul_zero, χ.elementCoeff_zero]
  · rw [negativeAngularTwist_apply _ _ _ ha]
    exact elementHom_negative_type χ order hk a ha

theorem actual_negative_ideal_factor (χ : AngularCharacter) (order q : ℕ)
    (hk : χ.k = -(order : ℤ))
    (hzero : order ≠ 0 ∨ finiteResidueHom χ 0 = 0)
    (hq : fixedBaseConductor q ≤ χ.modulus) :
    HasNegativeAngularFactor order q (elementCharacter χ.idealHom.toMonoidHom) := by
  refine ⟨finiteResidueHom χ, finiteResidueHom_norm_le_one χ, ?_, ?_⟩
  · intro x y hxy
    exact finiteResidueHom_factorsModulo χ x y (hq hxy)
  · have he : elementCharacter χ.idealHom.toMonoidHom = χ.elementHom.toMonoidHom := by
      ext a
      exact χ.idealHom_span a
    rw [he]
    exact actual_negative_element χ order hk hzero

#print axioms actual_negative_ideal_factor
#print axioms factor_norm_le_one
end OAI.CubicEisenstein.AngularIdealFactor
