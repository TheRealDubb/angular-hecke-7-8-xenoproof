import AngularControlledBounds

/-! Exact recovery of the original order-zero kernel, and the genuine
angular completed coefficient as a full-index reflected series. -/

noncomputable section
open scoped Classical BigOperators ContDiff

namespace OAI.CubicEisenstein.AngularControlledScalar

open CompletedGauss CompletedDyadic SevenEighths.Angular ConcreteTraceCRT
open AngularPhysicalSmoothedReflection AngularFiniteProjector AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O

theorem initialScalar_ne_zero (n : ℕ) : initialScalar n ≠ 0 := by
  unfold initialScalar
  exact mul_ne_zero thetaDerivativeScalar_ne_zero (pow_ne_zero _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (star_ne_zero.mpr thetaFrequencyScale_ne_zero)))

theorem normalized_reflection_zero (d : SourceCuspDatum) (W : ℝ → ℂ) (X : ℝ) :
    datumSmoothedDual 0 d (Vstar W) X / initialScalar 0 =
      d.smoothedKernel W X / thetaDerivativeScalar := by
  rw [normalized_reflection_full_index]
  calc
    _ = (d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2 /
        thetaDerivativeScalar) *
      ∑' p : ThetaFullIndex,
        sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p) *
          CubicReflectionKernel.paperKernel (Vstar W)
            (X * sourceCuspRadialLength (thetaFullFrequency p) /
              (27 * sourceCuspScale d.index ^ 2 * d.heightScale ^ 2)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      rw [normalizedTerm, normalizedScalar_zero, pow_zero, mul_one,
        AngularReflectionKernel.paperKernel_zero, physical_kernel_argument]
      ring
    _ = _ := by
      rw [d.smoothedKernel_full_index]
      ring

theorem completedT_full_index_reflection (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT χ.elementHom.toMonoidHom W X =
      ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient (finiteResidueHom χ) c) h *
          ∑' p : ThetaFullIndex, normalizedTerm n (finiteTwistCusp c hc h)
            (Vstar W) X (thetaFullFrequency p) := by
  have he := completedT_reflection χ n hk c hc hcQ W a b ha hWs hW X hX
  change initialScalar n * completedT χ.elementHom.toMonoidHom W X = _ at he
  apply mul_left_cancel₀ (initialScalar_ne_zero n)
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← normalized_reflection_full_index]
  field_simp [initialScalar_ne_zero n]

#print axioms normalized_reflection_zero
#print axioms completedT_full_index_reflection

end OAI.CubicEisenstein.AngularControlledScalar
