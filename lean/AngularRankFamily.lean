import AngularCanonicalCoefficient
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankFamilyGates

/-! Ray-family closure keeps the infinite angular factor explicit.
Periodicity is proved only for the reconstructed finite factor. -/
namespace OAI.CubicEisenstein.AngularRankFamily
open SevenEighths SevenEighths.InverseMoment CanonicalCoefficientClass
open AngularCanonicalCoefficient SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem angular_ray_finite_factor (order : ℕ) (base Ψ : O →* ℂ)
    (hΨ : IsBaseRayTwist (negativeAngularTwist base order) Ψ) :
    ∃ φ : O →* ℂ, IsBaseRayTwist base φ ∧ Ψ = negativeAngularTwist φ order := by
  rcases hΨ with rfl | ⟨χ, rfl⟩
  · exact ⟨base, Or.inl rfl, rfl⟩
  · refine ⟨rayMonoid χ * base, Or.inr ⟨χ, rfl⟩, ?_⟩
    rw [mul_comm (rayMonoid χ) base, negativeAngularTwist_mul, mul_comm]

theorem angular_rank_family_gates (order q : ℕ) (base Ψ : O →* ℂ)
    (hb : ∀ x, ‖base x‖ ≤ 1) (hp : FactorsModulo (fixedBaseConductor q) base)
    (hΨ : IsBaseRayTwist (negativeAngularTwist base order) Ψ) :
    ∃ φ : O →* ℂ, IsBaseRayTwist base φ ∧ (∀ x, ‖φ x‖ ≤ 1) ∧
      FactorsModulo (fixedBaseConductor q) φ ∧ Ψ = negativeAngularTwist φ order := by
  obtain ⟨φ, hφ, he⟩ := angular_ray_finite_factor order base Ψ hΨ
  exact ⟨φ, hφ, hφ.norm_le hb, actual_rank_family_period q base φ hp hφ, he⟩

#print axioms angular_rank_family_gates
end
end OAI.CubicEisenstein.AngularRankFamily
