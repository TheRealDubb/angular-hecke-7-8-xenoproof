import AngularPhysicalDetectorActualPhysicalRowAnalytic
import OAI.NumberTheory.DirichletL.Detector.PhysicalReopen

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

theorem physical_spectral_reopen (η : AngularCharacter) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O)
    (hs : Supported (Ideal.span {s})) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, spectralSummand S D (baseRowCoefficient η C.Xi s hs) t p.1 p.2 *
      ∑' m : O, calibratedNumerator C (completedIndex p.1 p.2) m *
        sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) := by
  let F (m : O) (p : Ideal O × Ideal O) : ℂ :=
    C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      spectralSummand S D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m) t p.1 p.2
  have hfin := elementWindow_finite_support W hW K hK
  have hzero : ∀ m, m∉hfin.toFinset → ∀ p, F m p=0 := by
    intro m hm p
    have hz : W (elementNorm m/K)=0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
    simp only [F, hz, mul_zero, zero_mul]
  have hsum (m : O) : Summable (F m) :=
    (spectralRow_summable S D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m)
      (PhysicalDetectorProbe.rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m) t ht).mul_left _
  have he := finite_support_tsum_comm F hfin.toFinset hzero (fun m _ => hsum m)
  calc
    _ = ∑' m : O, ∑' p : Ideal O × Ideal O, F m p := by
      simp only [F, spectralRow, tsum_mul_left]
    _ = ∑' p : Ideal O × Ideal O, ∑' m : O, F m p := he
    _ = _ := by
      apply tsum_congr
      intro p
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold F
      rw [spectralSummand_row_separation]
      unfold calibratedNumerator
      ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physical_spectral_reopen
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.physical_spectral_reopen
