import AngularFullSeries

/-! Exact all-order fixed-cusp coefficient normalization and its finite
Fourier sum. No absolute value is taken before local cancellation. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularControlledScalar

open CompletedGauss CompletedDyadic SevenEighths.Angular CubicKubota ConcreteTraceCRT
open AngularPhysicalSmoothedReflection
local notation "Eis" => ActualEisensteinCubic.O

def fullIndexDenominator (p : ThetaFullIndex) : ℂ :=
  ((ramifiedScale 1 completedRamifiedStep p.2.1 *
    Real.sqrt (Ideal.absNorm p.2.2.1.val : ℝ) *
      (Ideal.absNorm p.2.2.2.val : ℝ) : ℝ) : ℂ)

theorem fixedCusp_normalized_coefficient (n : ℕ) {H : SL(2,Eis)}
    (s : FixedCuspShape H) (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hC : ((g : SL(2,Eis)) * H) 1 0 = c) (p : ThetaFullIndex) :
    normalizedScalar n (s.datum g (by rwa [hC])) *
      sourceCuspRadialCoefficient s.index (s.datum g (by rwa [hC])).dualPoint
        (thetaFullFrequency p) * alpha (thetaFullFrequency p) ^ n =
    (fixedRadialCoefficientScalar / thetaDerivativeScalar * s.stratumShapeFactor c *
      shapeOrderPhase s c ^ n) *
      (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
        alpha (thetaFullFrequency p) ^ n / fullIndexDenominator p) *
      (star (levelTwoComplexCharacter g) *
        ShortDraftTrace.breveE (-(eisEmbedding (((g : SL(2,Eis)) * H) 1 1) *
          (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0)
            (thetaFullFrequency p)) / eisLam ^ 4)) / eisEmbedding c)) := by
  let d := s.datum g (by rwa [hC])
  have hindex : d.index = s.index := rfl
  have hheight : d.heightScale = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
    simpa only [d, hC, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using
      s.datum_heightScale g (by rwa [hC])
  have hrow : d.multiplier * (d.heightScale : ℂ) =
      s.stratumShapeFactor c * star (levelTwoComplexCharacter g) := by
    rw [hheight]
    exact s.datum_common_row_factor g c hc hC
  have he := d.smoothedFullCoefficient_normalization p
  have hp := s.datum_integral_phase g c hc hC p
  rw [normalizedScalar_eq, fixedCusp_orderPhase s g c hc hC, normalizedScalar_zero]
  change (d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2 /
    thetaDerivativeScalar * shapeOrderPhase s c ^ n) *
    sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p) *
    alpha (thetaFullFrequency p) ^ n = _
  calc
    _ = (shapeOrderPhase s c ^ n / thetaDerivativeScalar) *
        ((d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2) *
          sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)) *
            alpha (thetaFullFrequency p) ^ n := by ring
    _ = _ := by
      rw [he, hrow]
      simp only [hindex]
      change _ * (fixedRadialCoefficientScalar * _ *
        ((fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
          sourceFrequencyAngle (thetaFullFrequency p)) *
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p) *
            ((s.datum g _).dualPoint / (sourceCuspScale s.index : ℂ)))) / _) * _ = _
      rw [hp]
      unfold fullIndexDenominator
      ring

def fixedSeriesTerm (n : ℕ) {H : SL(2,Eis)} (s : FixedCuspShape H)
    (c : Eis) (V : ℝ → ℂ) (X : ℝ) (p : ThetaFullIndex) : ℂ :=
  (fixedRadialCoefficientScalar / thetaDerivativeScalar * s.stratumShapeFactor c *
    shapeOrderPhase s c ^ n) *
    (s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      alpha (thetaFullFrequency p) ^ n / fullIndexDenominator p) *
    AngularReflectionKernel.paperKernel n V
      (27 * thetaBesselScale ^ 2 * sourceCuspRadialScale s.index ^ 2 * X *
        sourceCuspRadialLength (thetaFullFrequency p) /
          (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2)

theorem fixedCusp_normalizedTerm (n : ℕ) {H : SL(2,Eis)}
    (s : FixedCuspShape H) (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hC : ((g : SL(2,Eis)) * H) 1 0 = c)
    (V : ℝ → ℂ) (X : ℝ) (p : ThetaFullIndex) :
    normalizedTerm n (s.datum g (by rwa [hC])) V X (thetaFullFrequency p) =
      fixedSeriesTerm n s c V X p *
      (star (levelTwoComplexCharacter g) *
        ShortDraftTrace.breveE (-(eisEmbedding (((g : SL(2,Eis)) * H) 1 1) *
          (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0)
            (thetaFullFrequency p)) / eisLam ^ 4)) / eisEmbedding c)) := by
  have hh : (s.datum g (by rwa [hC])).heightScale =
      (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
    simpa only [hC, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using
      s.datum_heightScale g (by rwa [hC])
  unfold normalizedTerm
  change (normalizedScalar n (s.datum g _) *
    sourceCuspRadialCoefficient s.index (s.datum g _).dualPoint (thetaFullFrequency p) *
      alpha (thetaFullFrequency p) ^ n) * _ = _
  rw [fixedCusp_normalized_coefficient n s g c hc hC p, hh]
  change _ * AngularReflectionKernel.paperKernel n V
    (27 * thetaBesselScale ^ 2 * sourceCuspRadialScale s.index ^ 2 * X *
      sourceCuspRadialLength (thetaFullFrequency p) /
        (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ 2) = _
  unfold fixedSeriesTerm
  ring

theorem sum_fixedCusp_normalized_reflection {ι : Type*} [Fintype ι]
    (n : ℕ) {H : SL(2,Eis)} (s : FixedCuspShape H)
    (g : ι → levelTwo) (c : Eis) (hc : c ≠ 0)
    (hC : ∀ v, ((g v : SL(2,Eis)) * H) 1 0 = c) (w : ι → ℂ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑ v, w v * (datumSmoothedDual n (s.datum (g v) (by rwa [hC v])) V X /
      initialScalar n)) =
    ∑' p : ThetaFullIndex, fixedSeriesTerm n s c V X p *
      ∑ v, w v * star (levelTwoComplexCharacter (g v)) *
        ShortDraftTrace.breveE (-(eisEmbedding (((g v : SL(2,Eis)) * H) 1 1) *
          (eisEmbedding (sourceCuspPhaseNumerator s.index (s.upper 0 0)
            (thetaFullFrequency p)) / eisLam ^ 4)) / eisEmbedding c) := by
  rw [finite_normalized_reflection n _ w V a b ha hVs hV X hX]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [fixedCusp_normalizedTerm n s (g v) c hc (hC v)]
  ring

#print axioms sum_fixedCusp_normalized_reflection

end OAI.CubicEisenstein.AngularControlledScalar
