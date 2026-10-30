import AngularPhysicalDetectorActualMeasurable
import AngularPhysicalDetectorCubeArithmetic
import OAI.NumberTheory.DirichletL.Detector.InitialScales

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def continuedPhysicalRowKernel {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z x w z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z)

def continuedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

def weightedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u P hPS W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

lemma weightedRowOnLines_eq {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ υ r t=
      (∏i,W i (((P i).val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold weightedRowOnLines continuedRowOnLines continuedPhysicalRowKernel calibratedTupleValue
  simp only [hnorm,Finset.prod_mul_distrib]
  ring
def cubeWeightedRow {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
    (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50))

theorem cube_sum_eq_common_profile {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) (t : HeightSpace) :
    (∑u∈R,∑P:(∀i,T i),cubeWeightedRow S hS hmax (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z a e H t)=
    {v : HeightSpace | (|v.1.1|≤H ∧ |v.2|≤H) ∧ |v.1.2|≤H}.indicator
      (fun v=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+v.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+v.2*Complex.I)
        ((17/50:ℂ)+v.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e v) t := by
  by_cases ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H
  · simp [cubeWeightedRow,ht,weightedRowOnLines,cubeArithmeticSum,
      Finset.mul_sum,mul_assoc]
  · simp [cubeWeightedRow,ht]

def commonCubeIntegrand {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
    (fun t=>sourceMellinWeight W0 W1 X Y Z
      (((a+16*e:ℝ):ℂ)+t.1.1*I) (((1-a-6*e:ℝ):ℂ)+t.2*I)
      ((17/50:ℂ)+t.1.2*I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)

def commonCubeIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫t,commonCubeIntegrand S hS hmax η R T hT W Yp W0 W1 X Y Z a e H t ∂heightMeasure

lemma cubeArithmeticSum_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) :
    Measurable (cubeArithmeticSum S hS hmax η R T hT W Yp a e) := by
  unfold cubeArithmeticSum
  apply Finset.measurable_sum
  intro u hu
  apply Measurable.mul
  · unfold frequencyWeight
    apply measurable_const_cpow
    · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
    · fun_prop
  · apply Finset.measurable_sum
    intro P hP
    exact calibratedTupleValue_measurable S hS hmax η u _ _ W Yp _ _ _
      (by fun_prop) (by fun_prop) (by fun_prop)

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.weightedRowOnLines_eq

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cube_sum_eq_common_profile

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cubeArithmeticSum_measurable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.cubeArithmeticSum_measurable
