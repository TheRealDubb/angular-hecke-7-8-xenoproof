import AngularPhysicalDetectorActualXBoundary

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

theorem right_x_integral_eq {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hl : 2≤l) (hr3 : r≤3) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_x_gaussian S hS hfirst hmax P hPS
    η u hu W0 W1 X Y Z hZ w z l r hl hr3 hw hz
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  exact (continuedPhysicalRowKernel_right_differentiableAt_x S hS hfirst hmax P hPS η u W0 W1
    X Y Z hZ x w z (hl.trans hx.1) hw hz).differentiableWithinAt

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.right_x_integral_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.right_x_integral_eq
