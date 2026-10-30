import AngularPhysicalDetectorActualSpectralPoisson
import OAI.NumberTheory.DirichletL.Detector.RadialSpectral

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

def radialMellinSpectralTerm (η : AngularCharacter) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

theorem transformedSpectralTerm_radial_mellin (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (D : Id)
    (s : O) (hs : Supported (Ideal.span {s})) (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (K σ : ℝ) (hK : 0<K) (hσ : 1<σ) (t : ℂ) (I J : Id) :
    transformedSpectralTerm η (calibrationForSet S hS) S D s hs W K t I J=
      radialMellinSpectralTerm η (calibrationForSet S hS) S D s hs W K σ t I J := by
  unfold transformedSpectralTerm radialMellinSpectralTerm
  split_ifs with hA
  · by_cases hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0
    · simp only [hz,zero_mul]
    · rw [actualFrequency_mellin S hS hSne (completedIndex I J) s hA (supportedElement_ne_zero s hs)
        ((spectralSummand_calibration_coprime S hS D I J _ t hz).mul_right hcs)
        W a b ha hW K hK σ hσ]
  · rfl


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.transformedSpectralTerm_radial_mellin
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.transformedSpectralTerm_radial_mellin
