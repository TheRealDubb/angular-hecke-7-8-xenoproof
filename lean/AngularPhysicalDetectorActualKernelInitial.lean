import AngularPhysicalDetectorActualPrincipalSplit
import AngularPhysicalDetectorActualCubeIntegral
import AngularPhysicalDetectorHighCompensatedContinuation

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

theorem continuedPhysicalRowKernel_initial {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (t : ProbeMellinBoundary.HeightSpace) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)=
    compensatedRowOnLines η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z ⟨u.val,u.property.1⟩ t := by
  unfold continuedPhysicalRowKernel physicalCompensatedRow compensatedRowOnLines
  rw [continuedCompensatedRow_eq_indexed S hS P hP hPS η u _ _ _
    (by norm_num) (by norm_num) (by norm_num)]
  ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_initial
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_initial
