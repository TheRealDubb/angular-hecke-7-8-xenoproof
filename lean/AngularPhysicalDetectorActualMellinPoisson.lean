import AngularPhysicalDetectorActualSpectralPoisson
import OAI.NumberTheory.DirichletL.Detector.MellinPoisson

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CubicEisenstein ProbePhysical ProbeMellinBoundary
open HeckeFamily HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

open scoped ContDiff
open CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge
open EisensteinSchwartzPoisson

theorem inner_mellin_poisson (η : AngularCharacter) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K Z : ℝ) (hK : 0<K) (hZ : 0<Z) :
    (∑' m : O, C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      verticalIntegral 4 (fun t => (Z:ℂ)^t * Complex.exp (t^2) *
        spectralRow C.excluded D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m) t)) =
    verticalIntegral 4 (fun t => (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      ((Z:ℂ)^t * Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D s hs W K t p.1 p.2) := by
  let c (m : O) := C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
    sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K)
  have hc : (Function.support c).Finite := by
    apply (elementWindow_finite_support W hWc K hK).subset
    intro m hm hz
    exact hm (by simp only [c, hz, mul_zero])
  rw [← finiteSupport_verticalIntegral c hc
    (fun m t => (Z:ℂ)^t * Complex.exp (t^2) *
      spectralRow C.excluded D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m) t) 4
    (fun m => physicalRow_integrable η C D s hs m Z hZ)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  norm_num only [Complex.ofReal_ofNat]
  have ht : 1 < ((4:ℂ)+(y:ℂ)*Complex.I).re := by simp
  rw [← physical_spectral_poisson η C C.excluded D s hs W hWc hWs K hK _ ht,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [c]
  ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.inner_mellin_poisson
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.inner_mellin_poisson
