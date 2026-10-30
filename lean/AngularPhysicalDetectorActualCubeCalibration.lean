import AngularPhysicalDetectorActualCubeFubini

namespace OAI

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

lemma cubeWeightedRow_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z a e H : ℝ) :
    cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H=0 := by
  funext t
  simp [cubeWeightedRow,weightedRowOnLines,calibratedTupleValue,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.Angular.PhysicalDetectorHigh

end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.centralCubeIntegral_calibration_zero

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cubeWeightedRow_calibration_zero

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_filter_calibration
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_filter_calibration
