import AngularPhysicalDetectorCentralTargetCost
import OAI.NumberTheory.DirichletL.PrimeRows.CoarseUniform

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail
  selectedFirstBound selectedFirstBound_nonneg selectedFirstBound_polynomial
  calibrated_numerator_first_uniform_growth rowNorm)
open ProbeRowRadicalConductor (fixedConductorConstant)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)
variable (angularOrder : ℕ)

theorem buffered_denominator_polynomial_growth (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : AngularCharacter) (u : FreeRow)
      (horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS η u j).residue≠1)
      (a B H : ℝ) (i : ℕ),(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS η u) hnp (3*(i+1:ℕ)*B)<a+2*e →
      ∀x : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H →
      ‖PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^2*(3+|H|)^2 := by
  obtain ⟨Cr,hCr,hbound⟩ := PhysicalDetectorControl.buffered_rectangle_reciprocal_bound
    angularOrder e 1 he he' (by norm_num)
  let F : ℝ := (fixedConductorConstant S:ℝ)
  refine ⟨2*Cr*(1+F^2),by positivity,?_⟩
  intro η u horder hnp a B H i ha haTop hB hH hbin x hxl hxr hxi
  have hH0 : 0≤H := (abs_nonneg _).trans hxi
  have hr : ‖PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS) x‖≤
      Cr*(PhysicalReciprocal.presentationComplexity ((SourceRows.targetRow η u).excludePrimes S hS) H)^(1:ℝ) :=
    hbound (SourceRows.sourceDetectorFamily M Hray hHray S hS η u)
      (fun j=>(PhysicalDetectorLiteralSource.literal_source_order M Hray hHray S hS η u j).trans horder)
      hnp B a H i hB ha haTop hH hbin (Sum.inl false) x hxl hxr hxi
  rw [Real.rpow_one] at hr
  have hc := target_complexity_norm_bound S hS η u H hH0
  rw [abs_of_nonneg hH0]
  apply hr.trans
  calc
    _ ≤ Cr*(2*(F*η.modulus.absNorm*rowNorm u)^2*(3+H)^2) :=
      mul_le_mul_of_nonneg_left hc hCr.le
    _ = (2*Cr*F^2)*((η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2) := by ring
    _ ≤ (2*Cr*(1+F^2))*((η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by unfold rowNorm;ring

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.buffered_denominator_polynomial_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.buffered_denominator_polynomial_growth
