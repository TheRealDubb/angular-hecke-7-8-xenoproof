import AngularControlledReflection

/-! Unit-modulus phase and exact radial scale of the all-order controlled
reflection. Constants in the kernel estimates may still depend on order. -/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace OAI.CubicEisenstein.AngularControlledScalar

open CompletedGauss CompletedDyadic SevenEighths.Angular ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem orderPhase_norm (d : SourceCuspDatum) : ‖orderPhase d‖ = 1 := by
  have hc : ‖d.matrix 1 0‖ ≠ 0 := norm_ne_zero_iff.mpr d.lower_ne_zero
  have hf : ‖thetaFrequencyScale‖ ≠ 0 := thetaBesselScale_pos.ne'
  rw [orderPhase, norm_div, norm_mul, norm_div, norm_neg,
    Complex.norm_of_nonneg d.heightScale_pos.le, norm_pow, norm_star]
  simp only [SourceCuspDatum.heightScale]
  field_simp

theorem shapeOrderPhase_norm {H : SL(2,Eis)} (s : FixedCuspShape H)
    (c : Eis) (hc : c ≠ 0) : ‖shapeOrderPhase s c‖ = 1 := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  have hf : ‖thetaFrequencyScale‖ ≠ 0 := thetaBesselScale_pos.ne'
  have hu : ‖eisEmbedding (s.upper 1 1)‖ = 1 := by
    rcases s.lower_unit with ⟨u, hu⟩
    rw [← hu]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [shapeOrderPhase, norm_div, norm_mul, norm_div, norm_neg,
    Complex.norm_of_nonneg (sq_nonneg _), norm_pow, norm_mul, hu, mul_one, norm_star]
  field_simp

theorem angular_amplitude_norm_le_one (n : ℕ) {H : SL(2,Eis)}
    (s : FixedCuspShape H) (p : ThetaFullIndex) :
    ‖s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      alpha (thetaFullFrequency p) ^ n‖ ≤ 1 := by
  rw [norm_mul, norm_pow, norm_alpha (thetaFullFrequency_ne_zero p), one_pow, mul_one]
  exact s.amplitude_norm _ _ _ _

theorem physical_kernel_argument (j : Fin 3) (Q X L : ℝ) :
    27 * thetaBesselScale ^ 2 * sourceCuspRadialScale j ^ 2 * X * L / Q ^ 2 =
      X * L / (27 * sourceCuspScale j ^ 2 * Q ^ 2) := by
  have ht : thetaBesselScale ^ 2 = 1 / 27 := by
    rw [thetaBesselScale_eq, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)]
    norm_num
  rw [sourceCuspRadialScale, div_pow, ht]
  ring

theorem physical_full_index_kernel_argument (j : Fin 3) (Q X : ℝ) (p : ThetaFullIndex) :
    27 * thetaBesselScale ^ 2 * sourceCuspRadialScale j ^ 2 * X *
        sourceCuspRadialLength (thetaFullFrequency p) / Q ^ 2 =
      (X / (27 * sourceCuspScale j ^ 2 * Q ^ 2)) *
        (ramifiedScale 1 completedRamifiedStep p.2.1) ^ 3 *
        (Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ) ^ 3 := by
  rw [physical_kernel_argument, sourceCusp_full_index_kernel_argument]

#print axioms angular_amplitude_norm_le_one
#print axioms physical_full_index_kernel_argument

end OAI.CubicEisenstein.AngularControlledScalar
