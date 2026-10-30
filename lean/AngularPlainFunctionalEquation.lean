import AngularFamilyContinuation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Reflection of the actual ordinary angular L-function. Identification with
the family continuation uses the physical ideal series and analytic uniqueness.
The statements here concern primitive finite residue and nonzero angular type. -/
noncomputable section
open scoped Classical Topology
open Set Filter Complex

namespace OAI.SevenEighths.Angular.PlainReflection

open ActualEisensteinCubic ConcreteTraceCRT ThetaContinuation ThetaTransform

variable (c : O) [NeZero c] (χ : AngularCharacter)
  (hmod : χ.modulus = Ideal.span {c})
  (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))

include hχ

def dualL (s : ℂ) : ℂ :=
  decompleteFactor c χ s * completedDual c χ hmod hχ s

theorem dualL_differentiable (hk : χ.k ≠ 0) :
    Differentiable ℂ (dualL c χ hmod hχ) :=
  (decompleteFactor_differentiable c χ).mul (completedDual_differentiable c χ hmod hχ hk)

theorem dualL_eq_series (s : ℂ) (hs : 1 < s.re) :
    dualL c χ hmod hχ s = χ.conjugate.series s := by
  rw [dualL,completedDual_eq_series c χ hmod hχ s hs]
  exact decompleteFactor_cancel c χ s (lt_trans zero_lt_one hs) _

theorem primitive_eq_family (hk : χ.k ≠ 0) (s : ℂ) :
    ThetaContinuation.LFunction c χ hmod hχ s = FamilyContinuation.LFunction χ s := by
  have he : ThetaContinuation.LFunction c χ hmod hχ =ᶠ[𝓝 (2:ℂ)]
      FamilyContinuation.LFunction χ := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2:ℂ), 1 < z.re :=
      Complex.continuous_re.continuousAt.tendsto.eventually
        (Ioi_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))
    filter_upwards [hn] with z hz
    rw [ThetaContinuation.LFunction_eq_series c χ hmod hχ z hz,
      FamilyContinuation.LFunction_eq_series χ z hz]
  exact congrFun (((ThetaContinuation.LFunction_differentiable c χ hmod hχ hk).differentiableOn.analyticOnNhd
    isOpen_univ).eq_of_eventuallyEq
    ((FamilyContinuation.LFunction_differentiable χ hk).differentiableOn.analyticOnNhd
      isOpen_univ) he) s

theorem dualL_eq_family (hk : χ.k ≠ 0) (s : ℂ) :
    dualL c χ hmod hχ s = FamilyContinuation.LFunction χ.conjugate s := by
  have hk' : χ.conjugate.k ≠ 0 := by simpa using hk
  have he : dualL c χ hmod hχ =ᶠ[𝓝 (2:ℂ)]
      FamilyContinuation.LFunction χ.conjugate := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2:ℂ), 1 < z.re :=
      Complex.continuous_re.continuousAt.tendsto.eventually
        (Ioi_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))
    filter_upwards [hn] with z hz
    rw [dualL_eq_series c χ hmod hχ z hz,
      FamilyContinuation.LFunction_eq_series χ.conjugate z hz]
  exact congrFun (((dualL_differentiable c χ hmod hχ hk).differentiableOn.analyticOnNhd
    isOpen_univ).eq_of_eventuallyEq
    ((FamilyContinuation.LFunction_differentiable χ.conjugate hk').differentiableOn.analyticOnNhd
      isOpen_univ) he) s

theorem completedDual_eq_family (hk : χ.k ≠ 0) (s : ℂ) (hs : 0 < s.re) :
    completedDual c χ hmod hχ s =
      Complex.Gamma (s+(χ.k.natAbs:ℂ)/2) *
        ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(-(s+(χ.k.natAbs:ℂ)/2)) *
        FamilyContinuation.LFunction χ.conjugate s := by
  have hb : ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_pos Real.pi_pos (GaussianTheta.parameter_pos c 1 zero_lt_one)).ne'
  have hd : decompleteFactor c χ s ≠ 0 := by
    unfold decompleteFactor
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hb))
      (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos (shifted_re_pos χ s hs)))
  apply mul_left_cancel₀ hd
  rw [decompleteFactor_cancel c χ s hs]
  exact dualL_eq_family c χ hmod hχ hk s

theorem functional_equation (hk : χ.k ≠ 0) (s : ℂ) (hs : s.re < 1) :
    FamilyContinuation.LFunction χ s =
      epsilon c χ.k (hmod ▸ χ.residue) *
        ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(2*s-1) *
        (Complex.Gamma (1-s+(χ.k.natAbs:ℂ)/2) /
          Complex.Gamma (s+(χ.k.natAbs:ℂ)/2)) *
        FamilyContinuation.LFunction χ.conjugate (1-s) := by
  have hb : ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (mul_pos Real.pi_pos (GaussianTheta.parameter_pos c 1 zero_lt_one)).ne'
  have he := completed_functional_equation c χ hmod hχ (1-s)
  rw [sub_sub_cancel] at he
  rw [←primitive_eq_family c χ hmod hχ hk s,ThetaContinuation.LFunction,he,
    completedDual_eq_family c χ hmod hχ hk (1-s) (by simp; linarith),decompleteFactor]
  have hp : ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(s+(χ.k.natAbs:ℂ)/2) *
      ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(-(1-s+(χ.k.natAbs:ℂ)/2)) =
      ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(2*s-1) := by
    rw [←Complex.cpow_add _ _ hb]
    congr 1
    ring
  calc
    _ = epsilon c χ.k (hmod ▸ χ.residue) *
        (((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(s+(χ.k.natAbs:ℂ)/2) *
          ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(-(1-s+(χ.k.natAbs:ℂ)/2))) *
        (Complex.Gamma (1-s+(χ.k.natAbs:ℂ)/2) *
          (Complex.Gamma (s+(χ.k.natAbs:ℂ)/2))⁻¹) *
        FamilyContinuation.LFunction χ.conjugate (1-s) := by ring
    _ = _ := by rw [hp]; simp only [div_eq_mul_inv]

end OAI.SevenEighths.Angular.PlainReflection
