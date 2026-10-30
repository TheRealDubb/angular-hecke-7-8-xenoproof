import AngularPolynomial
import AngularPlaneVolume
import OAI.NumberTheory.DirichletL.CubicSieve.RankMargins

noncomputable section
open scoped Classical SchwartzMap FourierTransform ContDiff
namespace OAI.SevenEighths.Angular.AnnularSchwartz
open OAI.SevenEighths.Angular.Polynomial CompletedHeight EisensteinSchwartzPoisson ConcreteTraceCRT

def reciprocalWeight (k : ℤ) (a b : ℝ) (ha : 0<a) (x : ℝ) : ℂ :=
  ((positiveCutoff a b ha x)*Real.exp (-(k.natAbs:ℝ)*(patchedLog a b ha x/2)):ℝ)

theorem reciprocalWeight_temperate (k : ℤ) (a b : ℝ) (ha : 0<a) :
    Function.HasTemperateGrowth (reciprocalWeight k a b ha) := by
  have hs : ContDiff ℝ ∞ (fun x=>Real.exp (-(k.natAbs:ℝ)*(patchedLog a b ha x/2))) :=
    (contDiff_const.mul ((patchedLog_temperate a b ha).1.div_const 2)).exp
  have hc : HasCompactSupport (reciprocalWeight k a b ha) := by
    exact (((positiveCutoff a b ha).hasCompactSupport.mul_right).comp_left (by simp))
  apply hc.hasTemperateGrowth
  exact Complex.ofRealCLM.contDiff.comp ((positiveCutoff a b ha).contDiff.mul hs)

theorem reciprocalWeight_norm_sq (k : ℤ) (a b : ℝ) (ha : 0<a) (z : ℂ)
    (hz : z≠0) (hs : ‖z‖^2 ∈ Set.Icc a b) :
    reciprocalWeight k a b ha (‖z‖^2) = ((‖z‖:ℂ)^k.natAbs)⁻¹ := by
  rw [reciprocalWeight,positiveCutoff_one a b ha _ hs,one_mul,patchedLog_eq_log a b ha _ hs]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have he : -(k.natAbs:ℝ)*(2*Real.log ‖z‖/2)= -((k.natAbs:ℝ)*Real.log ‖z‖) := by ring
  rw [he,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (norm_pos_iff.mpr hz)]
  push_cast
  rfl

theorem harmonic_temperate (k : ℤ) : Function.HasTemperateGrowth (harmonic k) := by
  unfold OAI.SevenEighths.Angular.Polynomial.harmonic
  split_ifs
  · fun_prop
  · change Function.HasTemperateGrowth (fun z => (Complex.conjCLE z)^k.natAbs)
    fun_prop

def annularCLM (k : ℤ) (a b : ℝ) (ha : 0<a) : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (harmonic k)).restrictScalars ℝ).comp
    (radialTestCLM.comp ((SchwartzMap.smulLeftCLM ℂ (reciprocalWeight k a b ha)).restrictScalars ℝ))

theorem annularCLM_raw (k : ℤ) (a b : ℝ) (ha : 0<a) (W : 𝓢(ℝ,ℂ)) (z : ℂ) :
    annularCLM k a b ha W z = harmonic k z*(reciprocalWeight k a b ha (‖z‖^2)*W (‖z‖^2)) := by
  change (SchwartzMap.smulLeftCLM ℂ (OAI.SevenEighths.Angular.Polynomial.harmonic k)
    (radialTest (SchwartzMap.smulLeftCLM ℂ (reciprocalWeight k a b ha) W))) z = _
  simp only [
    SchwartzMap.smulLeftCLM_apply_apply (harmonic_temperate k),
    radialTest_apply,
    SchwartzMap.smulLeftCLM_apply_apply (reciprocalWeight_temperate k a b ha),smul_eq_mul]

theorem annularCLM_apply (k : ℤ) (a b : ℝ) (ha : 0<a) (W : 𝓢(ℝ,ℂ))
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) (z : ℂ) :
    annularCLM k a b ha W z = (z/(‖z‖:ℂ))^k*W (‖z‖^2) := by
  rw [annularCLM_raw]
  by_cases hw : W (‖z‖^2)=0
  · simp only [hw,mul_zero]
  have hsz := hs hw
  have hz : z≠0 := by
    intro hz
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)] at hsz
    linarith [hsz.1]
  rw [reciprocalWeight_norm_sq k a b ha z hz hsz,harmonic_phase k z hz]
  have hr : (‖z‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  field_simp

theorem phase_div_positive (z : ℂ) (r : ℝ) (hr : 0<r) :
    (z/(r:ℂ))/(‖z/(r:ℂ)‖:ℂ)=z/(‖z‖:ℂ) := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,Complex.ofReal_div]
  exact div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr hr.ne') _ _

theorem annularCLM_scaled (k : ℤ) (a b : ℝ) (ha : 0<a) (W : 𝓢(ℝ,ℂ))
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) (X : ℝ) (hX : 0<X) (z : ℂ) :
    annularCLM k a b ha W (z/(Real.sqrt X:ℂ)) =
      (z/(‖z‖:ℂ))^k*W (‖z‖^2/X) := by
  rw [annularCLM_apply k a b ha W hs,phase_div_positive z _ (Real.sqrt_pos.mpr hX)]
  rw [norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg X),Real.sq_sqrt hX.le]

theorem annular_fourier_control (k : ℤ) (a b : ℝ) (ha : 0<a) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧ ∀ W,
      PlaneVolume.fourierControl (annularCLM k a b ha W) ≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  PlaneVolume.plane_source_control (annularCLM k a b ha)

end OAI.SevenEighths.Angular.AnnularSchwartz
