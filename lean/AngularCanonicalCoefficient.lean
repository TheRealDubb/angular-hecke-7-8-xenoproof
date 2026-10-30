import AngularReflectionCompatibility

/-! The canonical coefficient keeps its finite factor periodic and its
angular factor separate. No periodicity of the entire coefficient is asserted.
The coefficient identities adapt the inspected S3 AngularCompletedCoefficient. -/

noncomputable section
open scoped Classical BigOperators

namespace OAI.CubicEisenstein.AngularCanonicalCoefficient

open CompletedGauss SevenEighths.Angular ConcreteTraceCRT
open AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O

def negativeAngularTwist (Φ : Eis →* ℂ) (n : ℕ) : Eis →* ℂ where
  toFun a := star (alpha a) ^ n * Φ a
  map_one' := by simp
  map_mul' a b := by
    simp only [alpha_mul, star_mul, mul_pow, map_mul]
    ring

theorem negativeAngularTwist_apply (Φ : Eis →* ℂ) (n : ℕ)
    (a : Eis) (ha : a ≠ 0) :
    negativeAngularTwist Φ n a = alpha a ^ (-(n : ℤ)) * Φ a := by
  rw [alpha_neg_zpow ha, zpow_natCast, star_pow]
  rfl

theorem negativeAngularTwist_norm_le_one (Φ : Eis →* ℂ) (n : ℕ)
    (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (a : Eis) :
    ‖negativeAngularTwist Φ n a‖ ≤ 1 := by
  have ha : ‖alpha a‖ ≤ 1 := by
    by_cases hz : a = 0
    · simp [hz, alpha, FiniteGaussPhase.angularFactor]
    · exact (norm_alpha hz).le
  change ‖star (alpha a) ^ n * Φ a‖ ≤ 1
  rw [norm_mul, norm_pow, norm_star]
  calc
    _ ≤ 1 * ‖Φ a‖ := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
    _ ≤ 1 := by simpa using hΦ a

theorem negativeAngularTwist_mul (Φ ρ : Eis →* ℂ) (n : ℕ) :
    negativeAngularTwist (Φ * ρ) n = negativeAngularTwist Φ n * ρ := by
  ext a
  change star (alpha a) ^ n * (Φ a * ρ a) = (star (alpha a) ^ n * Φ a) * ρ a
  ring

theorem completedCoefficient_negativeAngularTwist (Φ : Eis →* ℂ) (n : ℕ)
    (I J : NonzeroIdeal) (hI : primaryGenerator I.val ≠ 0)
    (hJ : primaryGenerator J.val ≠ 0) (hsq : Squarefree I.val) :
    alpha (primaryGenerator I.val * primaryGenerator J.val ^ 3) ^ (-(n : ℤ)) *
      completedMellinCoefficient Φ (I,J) =
        completedMellinCoefficient (negativeAngularTwist Φ n) (I,J) := by
  have hl : (completedMellinLength (I,J) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (completedMellinLength_pos (I,J)).ne'
  apply mul_right_cancel₀ hl
  rw [mul_assoc, completedCoefficient_mul_length _ I J hI hJ hsq,
    completedCoefficient_mul_length _ I J hI hJ hsq]
  have he := negativeAngularTwist_apply Φ n
    (primaryGenerator I.val * primaryGenerator J.val ^ 3) (mul_ne_zero hI (pow_ne_zero 3 hJ))
  simp only [map_mul, map_pow] at he
  calc
    _ = star (eisEmbedding (primaryGenerator I.val * primaryGenerator J.val ^ 3)) *
        (‖eisEmbedding (primaryGenerator J.val)‖ : ℂ) * gaussTwo I.val hI *
        (alpha (primaryGenerator I.val * primaryGenerator J.val ^ 3) ^ (-(n : ℤ)) *
          (Φ (primaryGenerator I.val) * Φ (primaryGenerator J.val) ^ 3)) := by ring
    _ = _ := by rw [← he]; ring

theorem thetaPair_negativeAngularTwist (Φ : Eis →* ℂ) (n : ℕ)
    (I J : NonzeroIdeal) (hI : primaryGenerator I.val ≠ 0)
    (hJ : primaryGenerator J.val ≠ 0) (hsq : Squarefree I.val) :
    (-2 * Real.pi * Complex.I *
      star (cuspFrequency (primaryGenerator I.val * primaryGenerator J.val ^ 3))) ^ (n+1) *
      fixedThetaTwist Φ (primaryGenerator I.val * primaryGenerator J.val ^ 3) *
      star (sourceResidualFourierCoefficient
        (primaryGenerator I.val * primaryGenerator J.val ^ 3)) =
    thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n *
      completedMellinCoefficient (negativeAngularTwist Φ n) (I,J) *
      ((completedMellinLength (I,J) : ℂ) *
        (Real.sqrt (completedMellinLength (I,J)) : ℂ) ^ n) := by
  rw [thetaPair_higher_derivative_coefficient _ I J hI hJ hsq n,
    completedCoefficient_negativeAngularTwist Φ n I J hI hJ hsq]

#print axioms completedCoefficient_negativeAngularTwist

end OAI.CubicEisenstein.AngularCanonicalCoefficient
