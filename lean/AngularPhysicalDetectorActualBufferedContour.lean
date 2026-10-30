import AngularPhysicalDetectorBufferedPhysical
import AngularPhysicalDetectorActualCubeIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.BufferedContour

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail
  selectedFirstBound selectedFirstBound_nonneg 
   rowNorm)
local notation "O" => HeckeFamily.O

lemma sourceMellinWeight_differentiable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) :
    Differentiable ℂ (fun x=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hz)

theorem continuedPhysicalRowKernel_buffered_differentiableAt_x {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnp : ((SourceRows.targetRow η u).excludePrimes S hS.prime).k≠0 ∨ ((SourceRows.targetRow η u).excludePrimes S hS.prime).residue≠1)
    (hnz : FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x :=
  (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    ((physicalCompensatedRow_buffered_differentiableAt_x eps heps S hS hfirst _
      (tupleOutside S P hPS) η u x w z hx hw hz hxw hnp hnz).const_mul _)

theorem buffered_x_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r T : ℝ)
    (hl : (51/100:ℝ)≤l) (hr : (51/100:ℝ)≤r) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hlw : 1+eps≤l+w.re) (hrw : 1+eps≤r+w.re)
    (hnp : ((SourceRows.targetRow η u).excludePrimes S hS.prime).k≠0 ∨ ((SourceRows.targetRow η u).excludePrimes S hS.prime).residue≠1)
    (hnz : ∀x∈(uIcc l r ×ℂ uIcc (-T) T),
      FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S hS.prime) x≠0) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro x hx
    have hxlo : min l r≤x.re := hx.1.1
    have hx' : (51/100:ℝ)≤x.re := (le_min hl hr).trans hxlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-w.re≤l) (by linarith : 1+eps-w.re≤r)).trans hxlo
      linarith
    exact (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hZ x w z hx' hw hz hxw hnp (hnz x hx)).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.sourceMellinWeight_differentiable_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_buffered_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.buffered_x_rectangle
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.buffered_x_rectangle
