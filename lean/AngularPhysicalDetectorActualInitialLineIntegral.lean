import AngularPhysicalDetectorActualUniformTail
import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport

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

open ProbeHighRowFamily (source_profile_arithmetic_tails)

def initialLineIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
      2 (1-a-6*e) (17/50) p ∂heightMeasure

theorem actual_first_line_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (υ r : ℝ) (hυ : υ∈Icc (-(1/100:ℝ)) (1/2)) (hr : (17/50:ℝ)≤r) (hr1 : r≤1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
  let N : ℕ := 0
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_first_polynomial K S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  let A := A0*contourArithmeticCost η u P
  have hA := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 r ⟨hr,hr1⟩ t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  exact ht'.1

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_first_line_integrable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_first_line_integrable
