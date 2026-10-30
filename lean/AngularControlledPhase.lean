import AngularControlledScalar
import OAI.NumberTheory.DirichletL.Descent.ControlledMultiplier

/-! The added angular scalar is constant across the actual controlled
finite Fourier variable. This does not yet prove the terminal energy bound. -/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace OAI.CubicEisenstein.AngularControlledScalar

open CubicKubota ConcreteTraceCRT ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

def shapeOrderPhase {H : SL(2,Eis)} (s : FixedCuspShape H) (c : Eis) : ℂ :=
  -((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) /
    (eisEmbedding c * eisEmbedding (s.upper 1 1)) ^ 2 *
      thetaFrequencyScale / star thetaFrequencyScale

theorem fixedCusp_orderPhase {H : SL(2,Eis)} (s : FixedCuspShape H)
    (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hC : ((g : SL(2,Eis)) * H) 1 0 = c) :
    orderPhase (s.datum g (by rwa [hC])) = shapeOrderPhase s c := by
  rw [orderPhase, s.datum_heightScale, s.datum_matrix,
    integralComplexMatrix_apply, upper_right_removed_bottom _ _ s.lower_zero, hC]
  simp only [map_mul, shapeOrderPhase]

theorem controlled_orderPhase {ι : Type*} [Fintype ι]
    {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
    orderPhase (D.datum hN hr hbase s hp hc0 v) =
      shapeOrderPhase s (c0 * ∏ i, p i) := by
  unfold ControlledStratumArithmetic.datum
  apply fixedCusp_orderPhase
  · exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  · rw [D.sourceGamma_mul, D.denominator]

theorem normalizedScalar_zero (d : SourceCuspDatum) :
    normalizedScalar 0 d =
      d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2 /
        thetaDerivativeScalar := by
  simp only [normalizedScalar, AngularProjectedReflection.datumMultiplier,
    AngularPhysicalSmoothedReflection.sourceCusp_scale_ratio, SourceCuspDatum.multiplier,
    pow_zero, mul_one, Nat.zero_add, pow_one]
  ring

theorem fixedCusp_normalizedScalar (n : ℕ) {H : SL(2,Eis)}
    (s : FixedCuspShape H) (g : levelTwo) (c : Eis) (hc : c ≠ 0)
    (hC : ((g : SL(2,Eis)) * H) 1 0 = c) :
    normalizedScalar n (s.datum g (by rwa [hC])) =
      (s.stratumShapeFactor c * (sourceCuspScale s.index : ℂ) ^ 2 /
        thetaDerivativeScalar * shapeOrderPhase s c ^ n) *
          star (levelTwoComplexCharacter g) := by
  rw [normalizedScalar_eq, fixedCusp_orderPhase s g c hc hC, normalizedScalar_zero]
  change ((s.datum g _).multiplier * ((s.datum g _).heightScale : ℂ) *
    (sourceCuspScale s.index : ℂ) ^ 2 / thetaDerivativeScalar) * _ = _
  have hh : (s.datum g (by rwa [hC])).heightScale =
      (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
    simpa only [hC, eisEmbedding_norm_sq_eq_absNorm_span] using
      s.datum_heightScale g (by rwa [hC])
  rw [hh, s.datum_common_row_factor g c hc hC]
  ring

#print axioms controlled_orderPhase
#print axioms fixedCusp_normalizedScalar

end OAI.CubicEisenstein.AngularControlledScalar
