import AngularPlainGamma
import AngularPlainFunctionalEquation

/-! Conductor and height control for the actual primitive angular reflection.
The constant is fixed for each angular order; no growing-order uniformity is
claimed and no moment or improved zero-free estimate is concluded here. -/
noncomputable section
open scoped Classical Topology
open Set Complex

namespace OAI.SevenEighths.Angular.PlainReflection

open ActualEisensteinCubic ConcreteTraceCRT ThetaTransform HeckeStripActual

theorem physical_scale_cpow (c : O) [NeZero c] (s : ℂ) :
    ((Real.pi*GaussianTheta.parameter c 1:ℝ):ℂ)^(2*s-1) =
      (HeckeStrip.completionScale (conductor c):ℂ)^(1-2*s) := by
  rw [completionScale_eq_inv,HeckePrimitive.scale,Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg
      (mul_nonneg Real.pi_pos.le (GaussianTheta.parameter_pos c 1 zero_lt_one).le),
    ←Complex.cpow_neg]
  congr 1
  ring

theorem primitive_reflected_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (c : O) [NeZero c] (χ : AngularCharacter)
      (hmod : χ.modulus = Ideal.span {c})
      (_hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue)),
      χ.k ≠ 0 → χ.k.natAbs = n → ∀ s : ℂ,
      -(1/10 : ℝ) ≤ s.re → s.re ≤ 1/2 →
      ‖FamilyContinuation.LFunction χ s‖ ≤
        C*(conductor c)^(1/2-s.re)*(3+|s.im|)^2 *
          ‖FamilyContinuation.LFunction χ.conjugate (1-s)‖ := by
  obtain ⟨C,hC,hgamma⟩ := gamma_ratio_fixed_degree n
  refine ⟨C,hC,?_⟩
  intro c _ χ hmod hχ hk hn s hl hr
  rw [functional_equation c χ hmod hχ hk s (by linarith),physical_scale_cpow,
    norm_mul,norm_mul,norm_mul,norm_epsilon c χ.k _ hχ,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (HeckeStrip.completionScale_pos _
      (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))),hn]
  have hscale := HeckeDyadicReflection.completionScale_rpow_le
    (lt_of_lt_of_le zero_lt_one (conductor_ge_one c)) (show 0≤1-2*s.re by linarith)
  have he : (1-2*s).re=1-2*s.re := by simp
  rw [he]
  have he' : (1-2*s.re)/2=1/2-s.re := by ring
  rw [he'] at hscale
  calc
    _ ≤ ((conductor c)^(1/2-s.re)*(C*(3+|s.im|)^2))*
        ‖FamilyContinuation.LFunction χ.conjugate (1-s)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hscale (hgamma s hl hr)
        (norm_nonneg _) (Real.rpow_nonneg
          (le_trans zero_le_one (conductor_ge_one c)) _)) (norm_nonneg _)
    _ = _ := by ring

end OAI.SevenEighths.Angular.PlainReflection
