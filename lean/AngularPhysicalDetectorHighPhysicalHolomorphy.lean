import AngularPhysicalDetectorHighSelectedHolomorphy

/- Actual angular adaptation of pinned OAI-003 source proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (rowCharacter unitPart unitPart_spec unitPart_coprime unitPart_ne_zero
  multiplicity_lt_six canonical_decomposition markExclusions markedSourceExclusions
  marked_firstTail FirstTail selected_V_ne_zero row_phase_ramified)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

def physicalCompensatedRow (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) : ℂ :=
  continuedCompensatedRow S hS T hT η u x w z
    (fun P=>star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x)
    (fun P=>(P.val.absNorm:ℂ)^(-w))

theorem physicalCompensatedRow_first_differentiableAt_x (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (hx : theta<x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hregular : PhysicalLogarithmicInput.regular ((SourceRows.targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx.le
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (PhysicalReciprocal.reciprocal_differentiableAt_of_regular_ne_zero ((SourceRows.targetRow η u).excludePrimes S hS.prime) (by linarith) hregular).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem physicalCompensatedRow_first_differentiableAt_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (hx : theta≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) (hpole : w≠1 ∨ (rowCharacter S hS.prime u).residue≠1) :
    DifferentiableAt ℂ (fun w=>physicalCompensatedRow S hS T hT η u x w z) w := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact ((HeckeOrigin.continued_differentiableAt _ hpole).const_mul _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact (continuedCompensatedLocal_differentiable_w η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z hx (by linarith)) w

theorem physicalCompensatedRow_first_differentiableAt_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (hx : theta≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>physicalCompensatedRow S hS T hT η u x w z) z := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx
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
        (by linarith) hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z hx (by linarith)

theorem unselectedCorrection_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (T : Finset PrimeIdeal) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ),
      theta≤x.re → (19/20:ℝ)≤w.re → (33/200:ℝ)≤z.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_subpower δ hδ
  exact ⟨C,hC,fun S hS T η u x w z hx hw hz=>
    hbound (markExclusions S T) (markedSourceExclusions S hS T) η u x w z hx hw hz⟩

theorem unselectedCorrection_first_subpower (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (T : Finset PrimeIdeal) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re → 1+eps≤x.re+w.re →
      ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := continuedCorrection_first_subpower δ hδ
  exact ⟨C,hC,fun eps S hS hfirst T η u x w z hx hw hz hxw=>
    hbound eps (markExclusions S T) (markedSourceExclusions S hS T) (marked_firstTail eps S hfirst T)
      η u x w z hx hw hz hxw⟩


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_first_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_first_differentiableAt_w

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physicalCompensatedRow_first_differentiableAt_z

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.unselectedCorrection_subpower

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.unselectedCorrection_first_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.unselectedCorrection_first_subpower
