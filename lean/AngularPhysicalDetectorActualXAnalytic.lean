import AngularPhysicalDetectorActualBufferedContour
import AngularPhysicalDetectorHighPhysicalHolomorphy

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

theorem regular_ne_zero_right (χ : AngularCharacter) {s : ℂ} (hs : 1<s.re) :
    PhysicalLogarithmicInput.regular χ s≠0 := by
  have hpos : 0<s.re := by linarith
  by_cases hp : χ.k=0 ∧ χ.residue=1
  · have h1 : s≠1 := by intro h;subst s;norm_num at hs
    rw [PhysicalLogarithmicInput.regular_eq_principal_factor χ hp.1 hp.2 hpos h1]
    have hplus : s+1≠0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
      linarith
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1)
      (FamilyContinuation.LFunction_ne_zero χ s hs)) hplus
  · have hnp : χ.k≠0 ∨ χ.residue≠1 := by tauto
    rw [PhysicalLogarithmicInput.regular_eq_nonprincipal χ hnp]
    exact FamilyContinuation.LFunction_ne_zero χ s hs

theorem continuedPhysicalRowKernel_right_differentiableAt_x {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (x w z : ℂ)
    (hx : 2≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x := by
  have ht : theta<x.re := (theta_bounds.2.trans_le (by linarith : (7/8:ℝ)≤x.re))
  have hp := physicalCompensatedRow_first_differentiableAt_x (1/2) (by norm_num)
    S hS (by norm_num;exact hfirst) _ (tupleOutside S P hPS) η u x w z ht
    (by linarith) hz (by linarith) (regular_ne_zero_right _ (by linarith))
  exact (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    (hp.const_mul _)

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.regular_ne_zero_right

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_right_differentiableAt_x
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_right_differentiableAt_x
