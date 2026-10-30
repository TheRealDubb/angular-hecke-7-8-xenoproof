import AngularPhysicalDetectorActualSpectralSeparation
import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic

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

theorem calibrated_rowCoefficient_apply (η : AngularCharacter) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m a = η.elementCoeff a * (C.Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  PhysicalDetectorProbe.rowCoefficient_apply_unit η C.Xi s hs m a (C.Xi_norm_one a ha hcop)

theorem physicalRow_integrable (η : AngularCharacter) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s})) (m : O)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((4 : ℂ) + y * Complex.I) *
      Complex.exp (((4 : ℂ) + y * Complex.I) ^ 2) *
      spectralRow C.excluded D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m) ((4 : ℂ) + y * Complex.I)) := by
  exact spectralRow_vertical_integrable C.excluded D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m)
    (fun a => PhysicalDetectorProbe.rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m a)
    4 (by norm_num) Z hZ


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_rowCoefficient_apply

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalRow_integrable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalRow_integrable
