import AngularPhysicalDetectorActualRightGrowth
import AngularPhysicalDetectorActualRowMeasurable
import OAI.NumberTheory.DirichletL.PrimeRows.ProfileIntegral

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

open ProbeHighRowFamily (source_profile_integral_bound)

lemma rowAmplitudeOnLines_right_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1) (σ υ r : ℝ) (hσ : 2≤σ) (hσ3 : σ≤3)
    (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_right_joint_growth S hS hfirst hmax _
    (tupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro t
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ3) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem continuedPhysicalRowKernel_right_integrable {K : ℕ}
    (σ υ r : ℝ) (hσ : 2≤σ) (hσ3 : σ≤3) (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure := by
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_right_bound S hS hmax hfirst P hPS η u hu σ υ r hσ hσ3 hυ hr
  have hm := rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ υ r
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hbound t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC _ hm.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  have hk : AEStronglyMeasurable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure := by
    have heq : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r=
        (fun t=>sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
          rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t) := by funext t;exact continuedRowOnLines_eq_amplitude ..
    rw [heq]
    exact hs.aestronglyMeasurable.mul hm.aestronglyMeasurable
  exact hi.mono' hk (Filter.Eventually.of_forall fun t=>by rw [continuedRowOnLines_eq_amplitude,norm_mul])


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowAmplitudeOnLines_right_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_right_integrable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_right_integrable
