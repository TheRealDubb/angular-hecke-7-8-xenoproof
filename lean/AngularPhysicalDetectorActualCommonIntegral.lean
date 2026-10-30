import AngularPhysicalDetectorActualCubeFubini

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail
  calibrated_numerator_first_growth selectedFirstBound selectedFirstBound_nonneg)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)
variable (angularOrder : ℕ)

theorem cube_common_profile_integral {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : AngularCharacter) (horder : η.k.natAbs≤angularOrder) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) 
    (hnp : ∀u∈R,∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
      (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1)
    (hbin : ∀u (hu : u∈R),PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) (hnp u hu) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1' : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
      (fun t=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
        ((17/50:ℂ)+t.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  have hh := finiteCentralCubeRows_eq_integral M Hray hHray angularOrder e he he' S hS hmax hfirst η horder R hR T hT
    (fun _=>a) (fun _=>B) (fun _=>H) (fun _=>i) hnp
    (fun u hu=>⟨ha,ha1,hB,hH,hbin u hu⟩) W Yp W0 W1 a0 b0 a1 b1 ha0 ha1' hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh ⊢
  simpa only [cube_sum_eq_common_profile] using hh


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cube_common_profile_integral
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.cube_common_profile_integral
