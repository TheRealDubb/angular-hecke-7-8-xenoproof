import AngularPhysicalDetectorActualWAnalytic

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

lemma sourceMellinWeight_differentiableAt_z (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w z : ℂ) (hz : 0<z.re) :
    DifferentiableAt ℂ (fun z=>sourceMellinWeight W0 W1 X Y Z x w z) z := by
  have hxc : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hzc : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hm := (ProbeRadialMellin.radial_mellin_analytic W0 z hz).differentiableAt
  unfold sourceMellinWeight
  fun_prop (disch := first | exact Or.inl hxc | exact Or.inl hzc)

theorem continuedPhysicalRowKernel_differentiableAt_z {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z := by
  have hm := sourceMellinWeight_differentiableAt_z W0 W1 X Y Z hX hZ x w z (by linarith)
  have hp : Differentiable ℂ (fun z : ℂ=>∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1)) := by
    apply Differentiable.fun_finsetProd
    intro i hi
    have hp0 := (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
    have hn : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (elementNorm_pos _ hp0).ne'
    exact (differentiable_id.sub_const 1).const_cpow (Or.inl hn)
  have hNu : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hfreq : Differentiable ℂ (fun z=>frequencyWeight z ⟨u.val,u.property.1⟩) :=
    differentiable_id.neg.const_cpow (Or.inl hNu)
  exact ((hm.mul (hp z)).mul (hfreq z)).mul
    ((physicalCompensatedRow_local_differentiableAt_z eps heps S hS hfirst _ (tupleOutside S P hPS) η u x w z hx hw hz hxw).const_mul _)


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.sourceMellinWeight_differentiableAt_z

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_differentiableAt_z
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_differentiableAt_z
