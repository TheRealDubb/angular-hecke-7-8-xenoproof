import AngularControlledMultiplier

/-! All-order physical reflection as an absolutely convergent full theta
index series. The cube index is unrestricted. No terminal estimate is asserted. -/

noncomputable section
open scoped Classical BigOperators ContDiff

namespace OAI.CubicEisenstein.AngularControlledScalar

open CompletedGauss CompletedDyadic SevenEighths.Angular
open AngularPhysicalSmoothedReflection AngularProjectedReflection
open AngularDualRadialCoefficients
local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

def initialScalar (n : ℕ) : ℂ :=
  thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n

def rawNormalizedPrefactor (n : ℕ) (d : SourceCuspDatum) : ℂ :=
  (datumMultiplier (n + 1) d * (d.heightScale : ℂ) ^ (n + 1) *
    ((thetaBesselScale / sourceCuspRadialScale d.index : ℝ) : ℂ) ^ (n + 2)) /
      initialScalar n

def normalizedTerm (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (X : ℝ) (h : Eis) : ℂ :=
  normalizedScalar n d * sourceCuspRadialCoefficient d.index d.dualPoint h *
    alpha h ^ n * AngularReflectionKernel.paperKernel n V
      (27 * thetaBesselScale ^ 2 * sourceCuspRadialScale d.index ^ 2 * X *
        sourceCuspRadialLength h / d.heightScale ^ 2)

theorem normalizedTerm_factor (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (X : ℝ) (h : Eis) :
    normalizedTerm n d V X h =
      rawNormalizedPrefactor n d * dualKernelTerm n d V X h := by
  unfold normalizedTerm normalizedScalar rawNormalizedPrefactor initialScalar dualKernelTerm
  ring

theorem normalizedTerm_norm_summable (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun h : Eis => ‖normalizedTerm n d V X h‖) := by
  have hs := (dualKernelTerm_norm_summable n d V a b ha hVs hV X hX).mul_left
    ‖rawNormalizedPrefactor n d‖
  apply hs.congr
  intro h
  rw [normalizedTerm_factor, norm_mul]

theorem normalizedFullTerm_norm_summable (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun p : ThetaFullIndex =>
      ‖normalizedTerm n d V X (thetaFullFrequency p)‖) :=
  (normalizedTerm_norm_summable n d V a b ha hVs hV X hX).comp_injective
    thetaFullFrequency_injective

theorem normalized_reflection_full_index (n : ℕ) (d : SourceCuspDatum)
    (V : ℝ → ℂ) (X : ℝ) :
    datumSmoothedDual n d V X / initialScalar n =
      ∑' p : ThetaFullIndex, normalizedTerm n d V X (thetaFullFrequency p) := by
  calc
    _ = rawNormalizedPrefactor n d * ∑' h : Eis, dualKernelTerm n d V X h := by
      unfold datumSmoothedDual rawNormalizedPrefactor
      ring
    _ = ∑' h : Eis, normalizedTerm n d V X h := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      exact (normalizedTerm_factor n d V X h).symm
    _ = _ := by
      have he := sourceCuspRadialCoefficient_tsum_full_index d.index d.dualPoint
        (fun h => normalizedScalar n d * alpha h ^ n *
          AngularReflectionKernel.paperKernel n V
            (27 * thetaBesselScale ^ 2 * sourceCuspRadialScale d.index ^ 2 * X *
              sourceCuspRadialLength h / d.heightScale ^ 2))
      simpa only [normalizedTerm, mul_assoc, mul_comm, mul_left_comm] using he

theorem finite_normalized_reflection {ι : Type*} [Fintype ι]
    (n : ℕ) (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑ v, w v * (datumSmoothedDual n (d v) V X / initialScalar n)) =
      ∑' p : ThetaFullIndex, ∑ v, w v * normalizedTerm n (d v) V X (thetaFullFrequency p) := by
  rw [Summable.tsum_finsetSum (fun v _ =>
    ((normalizedFullTerm_norm_summable n (d v) V a b ha hVs hV X hX).of_norm).mul_left (w v))]
  apply Finset.sum_congr rfl
  intro v hv
  rw [tsum_mul_left, normalized_reflection_full_index]

#print axioms normalizedFullTerm_norm_summable
#print axioms finite_normalized_reflection

end OAI.CubicEisenstein.AngularControlledScalar
