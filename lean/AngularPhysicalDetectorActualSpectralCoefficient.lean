import AngularPhysicalDetectorActualSpectralSeparation
import AngularPhysicalDetectorActualPhysicalRowAnalytic
import OAI.NumberTheory.DirichletL.Detector.SpectralCoefficient

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

lemma baseRowCoefficient_unit_apply (η : AngularCharacter) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (A : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime C.generator A) :
    baseRowCoefficient η C.Xi s hs A=PhysicalDetectorProbe.targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s := by
  change PhysicalDetectorProbe.targetMonoid η A*star (C.Xi A)*sexticReciprocityPhase s A=_
  have hc : star (C.Xi A)=(C.Xi A)⁻¹ := (Complex.inv_eq_conj (C.Xi_norm_one A hA hcop)).symm
  rw [hc]
  congr 1
  exact congrArg (fun n : ℤ=>(n:ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem spectralSummand_source_coefficient (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : AngularCharacter) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : ℂ) :
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J=
      completedMask S D I J *
        (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
          star (FiniteGaussPhase.angularFactor (completedIndex I J)*G (completedIndex I J))*
          PhysicalDetectorProbe.targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
          reciprocitySign (completedIndex I J) s) /
        ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
        (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  have hA := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  have hb := baseRowCoefficient_unit_apply η C s hs (completedIndex I J) hA hcop
  have hangle : FiniteGaussPhase.angularFactor (completedIndex I J)=
      FiniteGaussPhase.angularFactor (primaryGenerator I)*FiniteGaussPhase.angularFactor (primaryGenerator J)^3 := by
    rw [completedIndex,angularFactor_mul,show primaryGenerator J^3=(primaryGenerator J*primaryGenerator J)*primaryGenerator J by ring,
      angularFactor_mul,angularFactor_mul]
    ring
  have hm : baseRowCoefficient η C.Xi s hs (primaryGenerator I)*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3=
        PhysicalDetectorProbe.targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*reciprocitySign (completedIndex I J) s := by
    rw [←map_pow,←map_mul]
    exact hb
  unfold spectralSummand CompletedGauss.columnWeight
  rw [completedCorrection_supported I J hI hJ,squarefreeGaussCoefficient_eq I hsf
    (supported_primaryGenerator_ne_zero I hI)]
  change _*(star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3/(Ideal.absNorm J:ℂ))*_=_
  rw [hangle]
  simp only [star_mul,star_pow]
  calc
    _ = completedMask S D I J*
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        (star (FiniteGaussPhase.angularFactor (primaryGenerator I))*
         star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3)*star (G (completedIndex I J))*
        (baseRowCoefficient η C.Xi s hs (primaryGenerator I)*baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3)) /
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ))*(fullIdealWeight t I*fullIdealWeight (3*t) J) := by ring
    _ = _ := by rw [hm];ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.baseRowCoefficient_unit_apply

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.spectralSummand_source_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.spectralSummand_source_coefficient
