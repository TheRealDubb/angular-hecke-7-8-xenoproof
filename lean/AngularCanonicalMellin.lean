import AngularCanonicalProjector

/-! Canonical finite factor times the genuine negative angular twist.
Adapted from pinned S3 AngularProjectedMellin; generic Mellin lemmas are reused.
Only Phi is periodic. Norm control, support, and convergence hypotheses remain explicit.
This proves a transform and its convergence, not a moment estimate. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace OAI.CubicEisenstein.AngularCanonicalMellin
open CompletedGauss SevenEighths.Angular AngularProjectedMellin
open AngularCanonicalCoefficient AngularCanonicalProjector
local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal Eis) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def canonicalRadialCoefficient (Φ : Eis →* ℂ) (n : ℕ)
    (p : CompletedMellinIndex) : ℂ :=
  completedMellinCoefficient (negativeAngularTwist Φ n) p *
    (Real.sqrt (completedMellinLength p) : ℂ) ^ n

/-- The weighted radial array is actually summable in the full original
absolute-convergence half-plane, with no additional summability premise. -/
theorem canonicalRadialCoefficient_summable (Φ : Eis →* ℂ) (n : ℕ)
    (hΦ : ∀ a, ‖Φ a‖ ≤ 1)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    Summable (fun p : CompletedMellinIndex => ‖canonicalRadialCoefficient Φ n p‖ *
      completedMellinLength p ^ (1 / 2 - (s + (n : ℂ) / 2).re)) := by
  have hnorm : ∀ a : Eis, ‖(negativeAngularTwist Φ n) a‖ ≤ 1 :=
    negativeAngularTwist_norm_le_one Φ n hΦ
  have hsum := completedMellinCoefficient_summable (negativeAngularTwist Φ n) hnorm
    (s.re - 1 / 2) (by linarith)
  apply hsum.congr
  intro p
  simp only [canonicalRadialCoefficient, norm_mul, norm_pow,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_assoc, sqrt_power_real_cancel _ (completedMellinLength_pos p) n s]
  congr 1
  congr 1
  ring

theorem canonicalRadialCoefficient_series (Φ : Eis →* ℂ) (n : ℕ) (s : ℂ) :
    (∑' p : CompletedMellinIndex, canonicalRadialCoefficient Φ n p *
      (completedMellinLength p : ℂ) ^ (1 / 2 - (s + (n : ℂ) / 2))) =
        completedDirichletSeries (negativeAngularTwist Φ n) s := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  rw [canonicalRadialCoefficient, mul_assoc,
    sqrt_power_complex_cancel _ (completedMellinLength_pos p) n s]

/-- The actual finite projector, rather than an assumed abstract profile,
is the radial Bessel profile with the extra physical derivative powers. -/
theorem physicalProjector_radial (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (v : ℝ) (hv : 0 < v) :
    physicalProjector Φ n c hc v =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        radialBesselProfile completedMellinLength (canonicalRadialCoefficient Φ n)
          thetaBesselScale v := by
  rw [physicalProjector_completed_indices Φ Q hperiod n c hc hcQ v hv]
  congr 1
  unfold radialBesselProfile
  apply tsum_congr
  intro p
  unfold canonicalRadialCoefficient
  ring

/-- Actual projected physical profile to actual angular completed
Dirichlet series, with every theta scalar and the shifted gamma factor. -/
theorem physicalProjector_mellin (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    mellin (physicalProjector Φ n c hc) (2 * s + (n : ℂ)) =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        besselMellinFactor thetaBesselScale (s + (n : ℂ) / 2) *
          completedDirichletSeries (negativeAngularTwist Φ n) s := by
  let A : ℂ := thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n
  let f : ℝ → ℂ := radialBesselProfile completedMellinLength
    (canonicalRadialCoefficient Φ n) thetaBesselScale
  have hp : mellin (physicalProjector Φ n c hc) (2 * s + (n : ℂ)) =
      mellin (fun v => A * f v) (2 * s + (n : ℂ)) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [physicalProjector_radial Φ Q hperiod n c hc hcQ v hv]
  have hmul := mellin_const_smul f (2 * s + (n : ℂ)) A
  simp only [smul_eq_mul] at hmul
  rw [hp, hmul]
  have ht : -(1 / 3 : ℝ) < (s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hm := radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (canonicalRadialCoefficient Φ n) thetaBesselScale thetaBesselScale_pos
    (s + (n : ℂ) / 2) ht (canonicalRadialCoefficient_summable Φ n hΦ s hs)
  rw [show (2 : ℂ) * (s + (n : ℂ) / 2) = 2 * s + (n : ℂ) by ring,
    canonicalRadialCoefficient_series Φ n s] at hm
  have hm' : mellin f (2 * s + (n : ℂ)) =
    besselMellinFactor thetaBesselScale (s + (n : ℂ) / 2) *
      completedDirichletSeries (negativeAngularTwist Φ n) s := by
    simpa only [f, besselMellinFactor,
      show (2 : ℂ) * (s + (n : ℂ) / 2) = 2 * s + (n : ℂ) by ring] using hm
  rw [hm']
  exact (mul_assoc _ _ _).symm

/-- The actual finite projector's Mellin integral exists throughout the
stated half-plane. There is no caller-supplied summability hypothesis. -/
theorem physicalProjector_mellinConvergent (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    MellinConvergent (physicalProjector Φ n c hc) (2 * s + (n : ℂ)) := by
  have ht : -(1 / 3 : ℝ) < (s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hi := radialBesselProfile_mellinConvergent completedMellinLength
    completedMellinLength_pos (canonicalRadialCoefficient Φ n) thetaBesselScale
    thetaBesselScale_pos (s + (n : ℂ) / 2) ht
    (canonicalRadialCoefficient_summable Φ n hΦ s hs)
  have hscaled := hi.const_smul
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n)
  rw [show (2 : ℂ) * (s + (n : ℂ) / 2) = 2 * s + (n : ℂ) by ring] at hscaled
  unfold MellinConvergent at hscaled ⊢
  apply (integrableOn_congr_fun (s := Ioi 0) (fun v hv => ?_) measurableSet_Ioi).mpr hscaled
  simp only [smul_eq_mul]
  rw [physicalProjector_radial Φ Q hperiod n c hc hcQ v hv]


#print axioms physicalProjector_mellin
#print axioms physicalProjector_mellinConvergent
end OAI.CubicEisenstein.AngularCanonicalMellin
