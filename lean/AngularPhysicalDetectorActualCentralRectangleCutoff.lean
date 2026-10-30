import AngularPhysicalDetectorActualCentralWTail
import AngularPhysicalDetectorActualBufferedIntegral

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

def centralRowIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

def centralRectangleIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ |t.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_row_w_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : AngularCharacter) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀(horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1),∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_w_height_tail M Hray hHray angularOrder K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS horder hnp X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let T : Set HeightSpace := {t | |t.1.1|≤H ∧ |t.2|≤H}
  let R : Set HeightSpace := {t | |t.1.1|≤H ∧ H < |t.2|}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.2|) by fun_prop) measurable_const)
  have hi : IntegrableOn f E heightMeasure := continuedPhysicalRowKernel_buffered_integrable M Hray hHray angularOrder e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu horder hnp hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hdiff : E\T=R := by
    ext t
    change (|t.1.1|≤H ∧ ¬(|t.1.1|≤H ∧ |t.2|≤H)) ↔ (|t.1.1|≤H ∧ H < |t.2|)
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,lt_of_not_ge (fun h=>hw ⟨hx,h⟩)⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,fun h=>not_le_of_gt hw h.2⟩
  have heq : centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=
      n*(∫t in R,f t ∂heightMeasure) := by
    rw [← hdiff,setIntegral_sdiff hT hi (fun t ht=>ht.1)]
    dsimp [centralRowIntegral,centralRectangleIntegral,n,E,T,f]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in R,‖f t‖ ∂heightMeasure) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left (hbound η u hu P hP hPS horder hnp X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
        (a+16*e) ⟨le_rfl,by linarith⟩) (norm_nonneg _)
    _ = _ := by ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.central_row_w_cutoff_error
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.central_row_w_cutoff_error
