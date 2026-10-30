import AngularPhysicalSmoothedReflection

/-! Exact phase, not merely norm, of the existing physical angular reflection.
This file proves no moment estimate or zero-free theorem. -/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace OAI.CubicEisenstein.AngularControlledScalar

open AngularPhysicalSmoothedReflection AngularProjectedReflection
open AngularDualRadialCoefficients

def normalizedScalar (n : ℕ) (d : SourceCuspDatum) : ℂ :=
  ((datumMultiplier (n + 1) d * (d.heightScale : ℂ) ^ (n + 1) *
      ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ) ^ (n + 2)) *
      extraScale d.index ^ n) /
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n)

def orderPhase (d : SourceCuspDatum) : ℂ :=
  -(d.heightScale : ℂ) / (d.matrix 1 0) ^ 2 *
    thetaFrequencyScale / star thetaFrequencyScale

theorem normalizedScalar_eq (n : ℕ) (d : SourceCuspDatum) :
    normalizedScalar n d = normalizedScalar 0 d * orderPhase d ^ n := by
  have hc := d.lower_ne_zero
  have hs : (sourceCuspScale d.index : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos d.index).ne'
  have ht := thetaDerivativeScalar_ne_zero
  have hf : thetaFrequencyScale ≠ 0 := norm_pos_iff.mp thetaBesselScale_pos
  have hfs : star thetaFrequencyScale ≠ 0 := by simpa using hf
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [normalizedScalar, sourceCusp_scale_ratio, datumMultiplier,
    extraScale, orderPhase, pow_zero, mul_one, Nat.zero_add]
  simp only [pow_add, mul_pow, div_pow, pow_mul, pow_one, pow_two]
  field_simp
  <;> ring

#print axioms normalizedScalar_eq

end OAI.CubicEisenstein.AngularControlledScalar
