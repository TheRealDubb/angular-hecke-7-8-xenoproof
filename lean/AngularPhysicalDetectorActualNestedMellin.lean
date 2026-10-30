import AngularPhysicalDetectorActualPhysicalRadial
import OAI.NumberTheory.DirichletL.Detector.OuterMellin

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

def nestedMellinPhysicalProbe (η : AngularCharacter) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      verticalIntegral υ (fun w=>(Y:ℂ)^(w-1)*(qs:ℂ)^(-w)*mellin W1 w*
        (CanonicalRowCompletion.idealRowHom C.generator s.val /
          (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ)))*
        verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
          ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
            (elementNorm C.generator*qs*X) ξ t p.1 p.2))
    else 0

lemma verticalIntegral_mul_const (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun s=>F s*c)=verticalIntegral σ F*c := by
  unfold verticalIntegral
  rw [integral_mul_const,mul_assoc]

theorem markedPhysicalProbe_eq_nested_mellin (η : AngularCharacter)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hξ : 1<ξ) :
    PhysicalDetectorProbe.markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      nestedMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z ξ υ := by
  rw [markedPhysicalProbe_eq_radial_mellin η S hS hSne D W0 W1 a0 b0 ha0 hW0 X Y Z ξ hX hZ hξ]
  unfold radialMellinPhysicalProbe nestedMellinPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    rw [verticalIntegral_mul_const,verticalIntegral_mul_const,
      ←outer_source_scaled_inverse W1 a1 b1 ha1 hW1 υ (Ideal.absNorm s.val:ℝ) Y
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)) hY]
    ring
  · simp only [mul_zero]


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.verticalIntegral_mul_const

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.markedPhysicalProbe_eq_nested_mellin
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.markedPhysicalProbe_eq_nested_mellin
