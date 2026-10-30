import AngularPhysicalDetectorActualFirstTransport
import AngularPhysicalDetectorActualInitialLineIntegral

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

open Filter
open scoped Topology
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions
  marked_firstTail FirstTail selectedFirstBound selectedFirstBound_nonneg
  calibrated_row_nonprincipal calibrated_numerator_first_growth)

theorem rowIntegral_eq_initialLineIntegral {K : ℕ}
    (a e : ℝ) (ha : (51/100:ℝ)≤a) (haTop : a≤1) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
        initialLineIntegral S hS hmax P hPS η u W0 W1 X Y Z a e :=
  (rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).2

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowIntegral_eq_initialLineIntegral
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowIntegral_eq_initialLineIntegral
