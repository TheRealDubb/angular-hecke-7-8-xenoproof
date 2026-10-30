import AngularPhysicalDetectorActualCubeIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.ProfileIntegral

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option diagnostics true
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

/-- Actual normalized central integral. Integrability follows from the
proved actual measurability and the displayed arithmetic bound. The bound
uses the full Mellin profile integral, with no cube-volume factor. The
arithmetic bound is supplied by actual_counted_central_bins for nonfloor
cells; floor cells and contour transport remain separate obligations. -/
theorem actual_common_cube_integral_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} (e a H : ℝ),0<e → e<1/1000 → 51/100≤a → a≤1 →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
      (η : AngularCharacter) (R : Finset FreeRow)
      (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : ℝ,0≤A →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤A) →
      Integrable (commonCubeIntegrand S hS hmax η R T hT W Yp W0 W1 X Y Z a e H) heightMeasure ∧
      ‖commonCubeIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z a e H‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K e a H he he' ha ha' S hS hmax η R T hT W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hE1 : MeasurableSet {t : HeightSpace | |t.1.1|≤H} :=
    measurableSet_le (by fun_prop) measurable_const
  have hE2 : MeasurableSet {t : HeightSpace | |t.2|≤H} :=
    measurableSet_le (by fun_prop) measurable_const
  have hE3 : MeasurableSet {t : HeightSpace | |t.1.2|≤H} :=
    measurableSet_le (by fun_prop) measurable_const
  have hE : MeasurableSet E := (hE1.inter hE2).inter hE3
  have hmV : Measurable V := by
    have hmV0 := (sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
      (a+16*e) (17/50) (1-a-6*e) (by norm_num)).measurable
    simpa [V] using hmV0
  have hmF : AEStronglyMeasurable F heightMeasure :=
    ((hmV.mul (cubeArithmeticSum_measurable S hS hmax η R T hT W Yp a e)).indicator hE).aestronglyMeasurable
  have hb' (t : HeightSpace) : ‖F t‖≤scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  have hf : Integrable F heightMeasure := hg.mono' hmF (Filter.Eventually.of_forall hb')
  refine ⟨hf,?_⟩
  change ‖((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure)‖≤_
  rw [norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring

lemma physical_central_mellin_scale (Z a e : ℝ) (hZ : 0<Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,
    ←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_common_cube_integral_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.physical_central_mellin_scale
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.physical_central_mellin_scale
