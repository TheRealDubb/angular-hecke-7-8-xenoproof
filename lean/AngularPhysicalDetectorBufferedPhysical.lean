import AngularPhysicalDetectorFirstSelectedHolomorphy
import AngularPhysicalDetectorHighPhysicalHolomorphy
import AngularPhysicalAnalyticEntireness

/- Local holomorphy of the actual angular row down to x.re=0.51.
The x derivative uses the actual denominator's nonvanishing at that point;
no global angular zero-free boundary or feedback inequality is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions
  marked_firstTail FirstTail)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

theorem reciprocal_nonprincipal_differentiableAt_of_nonzero (χ : AngularCharacter)
    (hnp : χ.k≠0 ∨ χ.residue≠1) (s : ℂ)
    (hnz : FamilyContinuation.LFunction χ s≠0) :
    DifferentiableAt ℂ (PhysicalReciprocal.reciprocal χ) s := by
  have he : PhysicalReciprocal.reciprocal χ=fun z=>(FamilyContinuation.LFunction χ z)⁻¹ :=
    funext (PhysicalReciprocal.reciprocal_eq_nonprincipal χ hnp)
  rw [he]
  exact (PhysicalAnalytic.nonprincipal_entire χ hnp s).inv hnz

theorem physicalCompensatedRow_buffered_differentiableAt_x
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnp : ((SourceRows.targetRow η u).excludePrimes S hS.prime).k≠0 ∨
      ((SourceRows.targetRow η u).excludePrimes S hS.prime).residue≠1)
    (hnz : FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (reciprocal_nonprincipal_differentiableAt_of_nonzero _ hnp x hnz).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z
        (by linarith) (by linarith)

theorem physicalCompensatedRow_local_differentiableAt_w
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>physicalCompensatedRow S hS T hT η u x w z) w := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact ((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact (continuedCompensatedLocal_first_differentiable_w η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z
        (by linarith) (by linarith)) w

theorem physicalCompensatedRow_local_differentiableAt_z
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  have hz1 : 6*z≠1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
    linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((HeckeFamily.LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z
        (by linarith) (by linarith)

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_buffered_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_local_differentiableAt_w

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_local_differentiableAt_z
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_local_differentiableAt_z
