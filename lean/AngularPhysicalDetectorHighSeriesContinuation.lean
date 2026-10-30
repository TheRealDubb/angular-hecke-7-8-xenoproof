import AngularPhysicalDetectorHighRowAgreement
import AngularPhysicalDetectorHighRowBoundary
import AngularPhysicalReciprocalRegular

/- Actual angular adaptation with explicit regular-function nonvanishing.
The conditional analytic assertions require later global or buffered zero control.
No historical zero supremum or improved ceiling is imported.
Adapted from pinned OAI-003 source proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (unitPart unitPart_coprime multiplicity_lt_six FirstTail
  firstPrimeDefectBound firstPrimeDefectBound_nonneg rowCharacter)
local notation "O" => ActualEisensteinCubic.O

attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

def continuedSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*HeckeFamily.LFunction (rowCharacter S hS.prime u) w*
    PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x*
      continuedCorrection S hS η u x w z

theorem continuedSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hx0 : x≠0 := by intro h; simp only [h,Complex.zero_re] at hx; linarith
  have hx1 : x≠1 := by intro h; simp only [h,Complex.one_re] at hx; linarith
  rw [continuedSeries,PhysicalReciprocal.reciprocal_eq_inv _ x (by linarith) (fun _ _=>hx1),
    high_L_factorization_continued S hS η u x w z hx hw hz,div_eq_mul_inv]

theorem continuedSeries_differentiableAt_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : theta<x.re) (hregular : PhysicalLogarithmicInput.regular ((SourceRows.targetRow η u).excludePrimes S hS.prime) x≠0)
    (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x =>continuedSeries S hS η u x w z) x := by
  exact ((PhysicalReciprocal.reciprocal_differentiableAt_of_regular_ne_zero ((SourceRows.targetRow η u).excludePrimes S hS.prime) ((show (0:ℝ)<theta by norm_num [theta]).trans hx) hregular).const_mul _).mul
    ((continuedCorrection_analytic_x S hS η u w z hw hz) x hx).differentiableAt

theorem continuedSeries_differentiableAt_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : theta≤x.re) (hw : (9/10 : ℝ)<w.re) (hz : (4/25 : ℝ)≤z.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w =>continuedSeries S hS η u x w z) w := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  exact (((HeckeFamily.LFunction_differentiableAt (rowCharacter S hS.prime u) hw0 hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_analytic_w S hS η u x z hx hz) w hw).differentiableAt

theorem continuedSeries_differentiableAt_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : theta≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)<z.re)
    (hpole : 6*z≠1) :
    DifferentiableAt ℂ (fun z =>continuedSeries S hS η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.mul_re] at he
    linarith
  exact ((((HeckeFamily.LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hpole)).comp z
    (differentiableAt_id.const_mul 6)).mul_const _).mul_const _).mul
      ((continuedCorrection_analytic_z S hS η u x w hx hw) z hz).differentiableAt

def continuedHighSeries (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeOrigin.continued (rowCharacter S hS.prime u) w*
    PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

theorem continuedHighSeries_eq_series (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) (hw0 : w≠0) (hw1 : w≠1) :
    continuedHighSeries S hS η u x w z=continuedSeries S hS η u x w z := by
  rw [continuedHighSeries,HeckeOrigin.continued_eq _ hw0 hw1,continuedSeries]

theorem continuedHighSeries_eq_initial (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedHighSeries S hS η u x w z=markedIdealHighSeries S 1 η u.val x w z := by
  have hw0 : w≠0 := by intro h; simp only [h,Complex.zero_re] at hw; linarith
  have hw1 : w≠1 := by intro h; simp only [h,Complex.one_re] at hw; linarith
  rw [continuedHighSeries_eq_series S hS η u x w z hw0 hw1,
    continuedSeries_eq_initial S hS η u x w z hx hw hz]

theorem continuedHighSeries_first_differentiableAt_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : max (-(1/100:ℝ)) (1+eps-x.re)<w.re)
    (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    ((continuedCorrection_first_analytic_w eps S hS hfirst η u x z hx hz) w hw).differentiableAt

theorem continuedHighSeries_first_differentiableAt_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hx : max (51/100:ℝ) (1+eps-w.re)<x.re)
    (hregular : PhysicalLogarithmicInput.regular ((SourceRows.targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>continuedHighSeries S hS η u x w z) x := by
  exact ((PhysicalReciprocal.reciprocal_differentiableAt_of_regular_ne_zero ((SourceRows.targetRow η u).excludePrimes S hS.prime) (by have hm := le_max_left (51/100:ℝ) (1+eps-w.re); linarith) hregular).const_mul _).mul
    ((continuedCorrection_first_analytic_x eps S hS hfirst η u w z hw hz) x hx).differentiableAt

theorem continuedHighSeries_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>continuedHighSeries S hS η u x w z) w := by
  exact (((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _).mul
    (continuedCorrection_first_boundary_w eps heps S hS hfirst η u x w z hx hw hz hxw).differentiableAt


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedHighSeries_eq_initial

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedSeries_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedSeries_differentiableAt_z

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedHighSeries_first_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedHighSeries_first_boundary_w
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedHighSeries_first_boundary_w
