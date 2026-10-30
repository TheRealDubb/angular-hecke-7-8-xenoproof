import AngularCanonicalReflection
import OAI.NumberTheory.DirichletL.Descent.ActiveReflection

/-! Exact marked reflection with only the finite factor periodic.
The signed mask expansion is the pinned original MarkedTwists identity.
No absolute values or row-count estimates are introduced here. -/

noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularMarkedReflection
open CompletedGauss CanonicalRowCompletion ConcreteTraceCRT
open SevenEighths.InverseMoment AngularCanonicalCoefficient
open AngularCanonicalReflection AngularControlledScalar AngularPhysicalSmoothedReflection
local notation "Eis" => ActualEisensteinCubic.O

def normalizedDual (n : ℕ) (d : SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  datumSmoothedDual n d (Vstar W) X / initialScalar n

theorem canonical_normalized_reflection (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ)
    (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (negativeAngularTwist Φ n) W X =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c) h *
          normalizedDual n (finiteTwistCusp c hc h) W X := by
  have he := AngularCanonicalReflection.completedT_reflection Φ Q hperiod n hΦ
    c hc hcQ W lo hi hlo hsupp hW X hX
  change initialScalar n * completedT (negativeAngularTwist Φ n) W X = _ at he
  apply mul_left_cancel₀ (initialScalar_ne_zero n)
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  unfold normalizedDual
  field_simp [initialScalar_ne_zero n]

theorem marked_canonical_reflection {ι : Type*} (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Φ : Eis →* ℂ) (hΦ : ∀ x, ‖Φ x‖ ≤ 1) (n : ℕ)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (negativeAngularTwist Φ n) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Φ c) h *
          normalizedDual n (finiteTwistCusp c hc h) W X := by
  have hnorm (T : Finset ι) : ∀ x, ‖(markTwist p T * Φ) x‖ ≤ 1 := by
    intro x
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (markTwist_norm p T x) (norm_nonneg _)).trans
      ((one_mul _).le.trans (hΦ x))
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Φ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_right hxy),
      hperiod x y (Ideal.mul_le_left hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Φ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (quotientTrace c hc)
            (fixedThetaQuotient (markTwist p T * Φ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Φ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  have htwist (T : Finset ι) : markTwist p T * negativeAngularTwist Φ n =
      negativeAngularTwist (markTwist p T * Φ) n := by
    ext a
    change markTwist p T a * (star (SevenEighths.Angular.alpha a) ^ n * Φ a) =
      star (SevenEighths.Angular.alpha a) ^ n * (markTwist p T a * Φ a)
    ring
  rw [markedCompletedT_prime_product_twists S p hp _ W hWcompact X hX]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
    completedT (markTwist p T * negativeAngularTwist Φ n) W X) = _
  simp_rw [htwist]
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient (markTwist p T * Φ) c) h *
            normalizedDual n (finiteTwistCusp c hc h) W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [canonical_normalized_reflection _ _ (hper T hT) n (hnorm T)
        c hc hcQ W lo hi hlo hsupp hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring

#print axioms marked_canonical_reflection
end OAI.CubicEisenstein.AngularMarkedReflection
