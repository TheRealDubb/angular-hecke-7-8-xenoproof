import AngularPhysicalDetectorActualSpectralCoefficient
import AngularPhysicalDetectorActualCoefficientDirect
import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
import OAI.NumberTheory.DirichletL.Detector.RadialIdentity

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

open CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
open scoped ContDiff

theorem physical_spectral_coefficient_scale (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : AngularCharacter) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (X : ℝ) (hX : 0<X) (t : ℂ) (H : O) :
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H =
    (Real.sqrt X:ℂ) * completedMask S D I J *
      calibratedHighCoefficient C η I (supported_primaryGenerator_ne_zero I hI) A s hA H /
      ((elementNorm A:ℂ)*(Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
      (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  dsimp only
  have hA := supportedElement_ne_zero (completedIndex I J) (supported_completed _ _
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
  have he := physical_poisson_prefactor (elementNorm C.generator) (elementNorm (completedIndex I J))
    (elementNorm s) X (elementNorm_pos _ C.generator_ne_zero) (elementNorm_pos _ hA)
    (elementNorm_pos _ (supportedElement_ne_zero s hs)) hX
  rw [spectralSummand_source_coefficient S D I J η C s hs hI hJ hsf hcop t]
  simp only [elementNorm_mul,Complex.ofReal_div,Complex.ofReal_mul] at he ⊢
  unfold calibratedHighCoefficient
  have htarget (a : O) : PhysicalDetectorProbe.targetMonoid η a=targetMonoid η a := rfl
  simp only [htarget]
  have hh := congrArg (fun v : ℂ=>v*
    (idealRowHom C.generator (Ideal.span {s})/(C.tau*C.residueMonoid s))*
    (completedMask S D I J *
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        star (FiniteGaussPhase.angularFactor (completedIndex I J)*ProbePhase.G (completedIndex I J))*
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
        ProbePhase.reciprocitySign (completedIndex I J) s)/
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)))*
    (fullIdealWeight t I*fullIdealWeight (3*t) J)*
    actualCongruenceCoefficient C (completedIndex I J) s hA H) he
  convert hh using 1 <;> ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physical_spectral_coefficient_scale
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.physical_spectral_coefficient_scale
