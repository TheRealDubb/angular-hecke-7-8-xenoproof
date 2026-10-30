import OAI.NumberTheory.DirichletL.Detector.MellinBoundary
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
import AngularPhysicalDetectorPhysicalProbe
import OAI.NumberTheory.DirichletL.Detector.SpectralSeparation

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

def baseRowCoefficient (η : AngularCharacter) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  PhysicalDetectorProbe.targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

theorem spectralSummand_row_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : AngularCharacter) (Xi : O →* ℂ) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    spectralSummand S D (PhysicalDetectorProbe.rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : PhysicalDetectorProbe.rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem calibrated_spectralSummand_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : AngularCharacter) (C : ProbePhysical.CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    C.residueMonoid m * spectralSummand S D (PhysicalDetectorProbe.rowCoefficient η C.Xi s hs m) t I J =
      ProbePhysical.calibratedNumerator C (completedIndex I J) m *
        spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J := by
  rw [spectralSummand_row_separation]
  unfold ProbePhysical.calibratedNumerator
  ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.spectralSummand_row_separation

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_spectralSummand_separation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_spectralSummand_separation
