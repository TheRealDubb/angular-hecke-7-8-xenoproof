import AngularCanonicalMellin

/-! Actual completed sum for finite Phi times the angular phase.
Adapted from the inspected pinned S3 projected reflection, shifted normalization,
contour, and physical smoothed reflection proofs. Only the finite factor is periodic.
Every integral interchange, continuation, and left-line integrability premise is
proved for the actual physical profile. This is not yet a moment estimate. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ContDiff MatrixGroups
namespace OAI.CubicEisenstein.AngularCanonicalReflection
open CompletedGauss SevenEighths.Angular ConcreteTraceCRT
open AngularCompletedCoefficient AngularProjectedReflection
open AngularHigherProfiles AngularHigherMellin AngularDualRadialCoefficients
open AngularShiftedBesselReflection AngularSmoothedReflection AngularSmoothingContour
open AngularPhysicalSmoothedReflection AngularControlledScalar
open AngularCanonicalCoefficient AngularCanonicalProjector AngularCanonicalMellin
local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

theorem physicalProjector_mellin_entire (Φ : Eis →* ℂ) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] :
    (∀ s : ℂ, MellinConvergent (physicalProjector Φ n c hc) s) ∧
    Differentiable ℂ (mellin (physicalProjector Φ n c hc)) := by
  apply finite_mellin_entire
  intro h
  exact translation_mellin_entire n c hc h

theorem physicalProjector_mellin_sum (Φ : Eis →* ℂ) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (s : ℂ) :
    mellin (physicalProjector Φ n c hc) s =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c) h *
          mellin (barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h)) s := by
  let weight := finiteAdditiveFourierCoeff (quotientTrace c hc)
    (fixedThetaQuotient Φ c)
  have hi (h : Eis ⧸ Ideal.span {c}) : IntegrableOn
      (fun v : ℝ => (v : ℂ) ^ (s - 1) * (weight h *
        barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h) v)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      ((translation_mellin_entire n c hc h).1 s).const_smul (weight h)
  unfold mellin physicalProjector
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun h hh => hi h)]
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [mellin, smul_eq_mul] using mellin_const_smul
    (barProfile cubicSourceConjugateFunction (n + 1) (thetaFourierTranslation c h)) s (weight h)


theorem continuedDirichlet_physicalProjector (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    continuedDirichlet n (physicalProjector Φ n c hc) thetaBesselScale s =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        completedDirichletSeries (negativeAngularTwist Φ n) s := by
  have ht : -(1 / 3 : ℝ) < (s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [continuedDirichlet, physicalProjector_mellin Φ Q hperiod n hΦ c hc hcQ s hs]
  have hi := inverseBesselMellinFactor_mul thetaBesselScale thetaBesselScale_pos
    (s + (n : ℂ) / 2) ht
  calc
    _ = (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        (inverseBesselMellinFactor thetaBesselScale (s + (n : ℂ) / 2) *
          besselMellinFactor thetaBesselScale (s + (n : ℂ) / 2)) *
        completedDirichletSeries (negativeAngularTwist Φ n) s := by ring
    _ = _ := by rw [hi, mul_one]


theorem physicalProjector_initial_integrable (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => smoothingIntegrand n (physicalProjector Φ n c hc)
      thetaBesselScale (Vstar W) X ((2 : ℂ) + t * Complex.I)) := by
  have hi := (completedT_initial_mellin_integrable (negativeAngularTwist Φ n)
    (negativeAngularTwist_norm_le_one Φ n hΦ) W a b ha hWs hW X hX).const_mul
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n)
  apply hi.congr
  filter_upwards with t
  rw [smoothingIntegrand, continuedDirichlet_physicalProjector Φ Q hperiod n hΦ c hc hcQ _ (by norm_num),
    show (2 : ℂ) + t * Complex.I - 1 / 2 = 3 / 2 + t * Complex.I by ring]
  ring

theorem physicalProjector_initial_mellin (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      completedT (negativeAngularTwist Φ n) W X =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          smoothingIntegrand n (physicalProjector Φ n c hc) thetaBesselScale (Vstar W) X
            ((2 : ℂ) + t * Complex.I) := by
  have hid (t : ℝ) :
      smoothingIntegrand n (physicalProjector Φ n c hc) thetaBesselScale (Vstar W) X
        ((2 : ℂ) + t * Complex.I) =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        (mellin (Vstar W) ((3 / 2 : ℂ) + t * Complex.I) *
          (X : ℂ) ^ ((3 / 2 : ℂ) + t * Complex.I) *
            completedDirichletSeries (negativeAngularTwist Φ n) ((2 : ℂ) + t * Complex.I)) := by
    rw [smoothingIntegrand, continuedDirichlet_physicalProjector Φ Q hperiod n hΦ c hc hcQ _ (by norm_num),
      show (2 : ℂ) + t * Complex.I - 1 / 2 = 3 / 2 + t * Complex.I by ring]
    ring
  simp_rw [hid]
  rw [integral_const_mul, completedT_initial_mellin (negativeAngularTwist Φ n)
    (negativeAngularTwist_norm_le_one Φ n hΦ) W a b ha hWs hW X hX]
  ring

/-- Global shift of the actual physical projector, retaining the exact
scalar and explicit left-line integrability. No reflection model is substituted. -/
theorem physicalProjector_mellin_shift (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * Q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) (lo : ℝ) (hlo : lo ≤ 2)
    (hleft : Integrable (fun t : ℝ => smoothingIntegrand n (physicalProjector Φ n c hc)
      thetaBesselScale (Vstar W) X ((lo : ℂ) + t * Complex.I))) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      completedT (negativeAngularTwist Φ n) W X =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          smoothingIntegrand n (physicalProjector Φ n c hc) thetaBesselScale (Vstar W) X
            ((lo : ℂ) + t * Complex.I) := by
  have hF := physicalProjector_mellin_entire Φ n c hc
  have he := smoothingIntegrand_contour_eq n (physicalProjector Φ n c hc)
    thetaBesselScale thetaBesselScale_pos hF.1 hF.2 (Vstar W) a b ha
    (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW) X hX lo 2 hlo
    hleft (physicalProjector_initial_integrable Φ Q hperiod n hΦ c hc hcQ W a b ha hWs hW X hX)
  rw [he]
  exact physicalProjector_initial_mellin Φ Q hperiod n hΦ c hc hcQ W a b ha hWs hW X hX


theorem physicalProjector_smoothingIntegrand_sum (Φ : Eis →* ℂ) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (V : ℝ → ℂ) (X : ℝ) (s : ℂ) :
    smoothingIntegrand n (physicalProjector Φ n c hc) thetaBesselScale V X s =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c) h *
          smoothingIntegrand n (barProfile cubicSourceConjugateFunction (n + 1)
            (finiteTwistCusp c hc h).point) thetaBesselScale V X s := by
  unfold smoothingIntegrand continuedDirichlet
  rw [physicalProjector_mellin_sum]
  simp only [Finset.mul_sum, finiteTwistCusp_point]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- The actual finite projector is integrable on the left line. -/
theorem physicalProjector_left_integrable (Φ : Eis →* ℂ) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => smoothingIntegrand n (physicalProjector Φ n c hc)
      thetaBesselScale V X ((-1 : ℂ) + t * Complex.I)) := by
  simp_rw [physicalProjector_smoothingIntegrand_sum]
  apply integrable_finsetSum
  intro h hh
  exact (datum_smoothing_integrable n (finiteTwistCusp c hc h) V a b ha hVs hV X hX).const_mul _

theorem physicalProjector_smoothing_integral (Φ : Eis →* ℂ) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      smoothingIntegrand n (physicalProjector Φ n c hc) thetaBesselScale V X
        ((-1 : ℂ) + t * Complex.I) =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c) h *
          datumSmoothedDual n (finiteTwistCusp c hc h) V X := by
  simp_rw [physicalProjector_smoothingIntegrand_sum]
  rw [integral_finsetSum Finset.univ (fun h hh =>
    (datum_smoothing_integrable n (finiteTwistCusp c hc h) V a b ha hVs hV X hX).const_mul _),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [integral_const_mul]
  calc
    _ = finiteAdditiveFourierCoeff (quotientTrace c hc)
        (fixedThetaQuotient Φ c) h *
        ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, smoothingIntegrand n
          (barProfile cubicSourceConjugateFunction (n + 1) (finiteTwistCusp c hc h).point)
          thetaBesselScale V X ((-1 : ℂ) + t * Complex.I)) := by ring
    _ = _ := by rw [datum_smoothing_integral n _ V a b ha hVs hV X hX]

/-- Full physical smoothed reflection of the actual completed angular sum.
The initial scalar, every finite Fourier weight, the matrix-dependent height
and cusp scale, and the normalized angular-phase coefficient are retained. -/
theorem completedT_reflection (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      completedT (negativeAngularTwist Φ n) W X =
        ∑ h : Eis ⧸ Ideal.span {c},
          finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c) h *
            datumSmoothedDual n (finiteTwistCusp c hc h) (Vstar W) X := by
  have hVs := Vstar_support W a b hWs
  have hV := Vstar_contDiff W a b ha hWs hW
  have hleft : Integrable (fun t : ℝ => smoothingIntegrand n (physicalProjector Φ n c hc)
      thetaBesselScale (Vstar W) X (((-1 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
      physicalProjector_left_integrable Φ n c hc (Vstar W) a b ha hVs hV X hX
  rw [physicalProjector_mellin_shift Φ Q hperiod n hΦ c hc hcQ W a b ha hWs hW X hX
    (-1) (by norm_num) hleft]
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
    physicalProjector_smoothing_integral Φ n c hc (Vstar W) a b ha hVs hV X hX


theorem completedT_full_index_reflection (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (negativeAngularTwist Φ n) W X =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient Φ c) h *
          ∑' p : ThetaFullIndex, normalizedTerm n (finiteTwistCusp c hc h)
            (Vstar W) X (thetaFullFrequency p) := by
  have he := completedT_reflection Φ Q hperiod n hΦ c hc hcQ W a b ha hWs hW X hX
  change initialScalar n * completedT (negativeAngularTwist Φ n) W X = _ at he
  apply mul_left_cancel₀ (initialScalar_ne_zero n)
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← normalized_reflection_full_index]
  field_simp [initialScalar_ne_zero n]


#print axioms physicalProjector_mellin_entire
#print axioms physicalProjector_mellin_shift
#print axioms completedT_full_index_reflection
end OAI.CubicEisenstein.AngularCanonicalReflection
