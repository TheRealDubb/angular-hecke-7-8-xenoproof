import OAI.NumberTheory.DirichletL.Detector.MellinBoundary
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows
import AngularPhysicalDetectorHighCoefficient
import OAI.NumberTheory.DirichletL.Detector.FrequencySupport

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

def calibratedHighCoefficient (C : CalibrationData) (η : AngularCharacter)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  actualCongruenceCoefficient C A s hA H * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * ProbePhase.G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

lemma div_mul_frequency_cancel (a b c m : ℂ) (hc : c≠0) :
    c*(a/(b*c)*m)=a/b*m := by
  simp only [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (c*c⁻¹)*(a*b⁻¹*m) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc,one_mul]

theorem calibratedHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    calibratedHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) H=
      star ((calibrationForSet S hS).residueMonoid H)*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  let C := calibrationForSet S hS
  by_cases hH : IsCoprime C.generator H
  · have hn : star (C.residueMonoid H)≠0 := by
      apply star_ne_zero.mpr
      exact C.residue.apply_ne_zero_iff.mpr ((CubicEisenstein.isUnit_quotient_span_iff C.generator H).mpr hH)
    have he := sourceHighCoefficient_eq_bare S hS η I hI A s hA hs hcop H 1 (by simpa using hH)
    simp only [one_pow,mul_one] at he
    rw [←he]
    unfold sourceHighCoefficient calibratedHighCoefficient
    simp only [one_pow,mul_one]
    symm
    convert div_mul_frequency_cancel
      (actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H * idealRowHom C.generator (Ideal.span {s}))
      ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s)
      (star (C.residueMonoid H))
      (gaussTwo I hI*star (FiniteGaussPhase.angularFactor A*ProbePhase.G A)*targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s)
      hn using 1 <;> dsimp only [C] <;> ring
  · have hz := actualCongruenceCoefficient_zero_off_calibration S hS A s
      (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) hcop H hH
    have hξ : C.residueMonoid H=0 := by
      change C.residue (Ideal.Quotient.mk _ H)=0
      apply MulChar.map_nonunit
      exact fun h=>hH ((CubicEisenstein.isUnit_quotient_span_iff _ _).mp h)
    dsimp only [C] at hξ
    simp only [calibratedHighCoefficient,hz,zero_mul,zero_div,hξ,star_zero]


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.div_mul_frequency_cancel

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibratedHighCoefficient_eq_bare
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibratedHighCoefficient_eq_bare
