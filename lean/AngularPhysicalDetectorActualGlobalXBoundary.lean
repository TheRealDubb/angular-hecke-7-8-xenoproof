import AngularPhysicalDetectorActualGlobalXGrowth
import AngularPhysicalDetectorActualXBoundary

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail)
local notation "O" => ActualEisensteinCubic.O

theorem continuedPhysicalRowKernel_global_x_gaussian (angularCap : ℕ) {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (hk : η.k≠0) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : (PhysicalZeroSupremum.beta angularCap)+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((v:ℂ)+t*I) w z‖≤
        B*Continuation.polynomialGaussian 2 (t+z.im) := by
  obtain ⟨C,hC,hrow⟩ := physicalRow_global_x_growth angularCap e eps he he' S hS hfirst _
    (tupleOutside S P hPS) η horder hk u w z l r hl hlβ hw hz hlw
  let A := ‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1)*
    Real.exp ((|z.re|+r+1)^2)*C
  have hA : 0≤A := by dsimp [A,scaleBound];positivity
  refine ⟨A*(2*(3+|z.im|)^2),by positivity,?_⟩
  intro v hv t
  have hZb := cpow_le_scaleBound hZ (((v:ℂ)+t*I)+z-1)
    (show (((v:ℂ)+t*I)+z-1).re∈Icc (l+z.re-1) (r+z.re-1) by
      simpa using And.intro (by linarith [hv.1] : l+z.re-1≤v+z.re-1)
        (by linarith [hv.2] : v+z.re-1≤r+z.re-1))
  have hgb := coupled_gaussian_bound z (by linarith : 0<l) hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u ((v:ℂ)+t*I) w z‖≤C*(3+|t|)^2 := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
    simpa using hrow ((v:ℂ)+t*I) (by simpa using hv.1) (by simpa using hv.2)
  rw [continuedPhysicalRowKernel_x_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1))*
        (Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)))*(C*(3+|t|)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZb (norm_nonneg _)) hgb
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (scaleBound_pos _ _ _).le))
        hr (norm_nonneg _) (by unfold scaleBound;positivity)
    _ = A*(3+|t|)^2*Real.exp (-((t+z.im)^2)) := by dsimp [A];ring
    _ ≤ A*(2*(3+|z.im|)^2*(1+|t+z.im|^2))*Real.exp (-((t+z.im)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Continuation.shifted_height_two t z.im) hA) (Real.exp_pos _).le
    _ = _ := by unfold Continuation.polynomialGaussian;ring

end SevenEighths.Angular.PhysicalDetectorHigh

end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_global_x_gaussian
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedPhysicalRowKernel_global_x_gaussian
