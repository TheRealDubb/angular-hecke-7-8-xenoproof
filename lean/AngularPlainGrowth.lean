import AngularPlainFunctionalEquation
import OAI.NumberTheory.DirichletL.Hecke.Strip

/-! Exponential growth is proved from the actual strong angular theta pair,
with the Mellin strip and inverse gamma strip both shifted by |k|/2. -/
noncomputable section
open scoped Classical Topology
open Set Filter MeasureTheory Complex
namespace OAI.SevenEighths.Angular.PlainReflection
open ActualEisensteinCubic ThetaContinuation

theorem shifted_uncompleted_exp_bound (b : ℝ) (hb : 0 < b) (n : ℕ) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ HeckeStrip.closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖(b:ℂ)^(z+(n:ℂ)/2) * (Complex.Gamma (z+(n:ℂ)/2))⁻¹ * F z‖ ≤
        A*Real.exp (B*|z.im|) := by
  obtain ⟨C,hC,hF⟩ := hF
  obtain ⟨G,hG,hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1/10)+(n:ℝ)/2) (11/10+(n:ℝ)/2)
  let S : ℝ := b^(-(1/10)+(n:ℝ)/2) + b^(11/10+(n:ℝ)/2)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hb.le _)
  refine ⟨S*G*C,Real.pi,by positivity,Real.pi_pos.le,?_⟩
  intro z hz
  have hzc : z ∈ HeckeStrip.closedStrip := ⟨hz.1.le,hz.2.le⟩
  have hbBound : ‖(b:ℂ)^(z+(n:ℂ)/2)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
    apply VerticalContourShift.rpow_between_endpoints b (-(1/10)+(n:ℝ)/2)
      (11/10+(n:ℝ)/2) _ hb
    · simp only [add_re,div_ofNat_re,natCast_re]; linarith [hz.1]
    · simp only [add_re,div_ofNat_re,natCast_re]; linarith [hz.2]
  have hgamma := hg (z+(n:ℂ)/2) (show
      -(1/10)+(n:ℝ)/2 ≤ (z+(n:ℂ)/2).re ∧
      (z+(n:ℂ)/2).re ≤ 11/10+(n:ℝ)/2 by
        simp only [add_re,div_ofNat_re,natCast_re]
        exact ⟨by linarith [hz.1],by linarith [hz.2]⟩)
  simp only [add_im,div_ofNat_im,natCast_im,zero_div,add_zero] at hgamma
  rw [norm_mul,norm_mul]
  have hprod := mul_le_mul (mul_le_mul hbBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem completed_strip_bounded (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue)) (hk : χ.k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ HeckeStrip.closedStrip,
      ‖completed c χ hmod hχ z‖ ≤ C := by
  let f : ℝ → ℂ := fun t => (pair c χ hmod hχ).f t / 6
  have hP := pair_strong c χ hmod hχ hk
  have hconv (s : ℂ) : MellinConvergent f s := (hP.hasMellin s).1.div_const 6
  obtain ⟨C,hC,hb⟩ := VerticalContourShift.mellin_uniform_strip_bound f
    (-(1/10)+(χ.k.natAbs:ℝ)/2) (11/10+(χ.k.natAbs:ℝ)/2)
    (hconv _) (hconv _)
  refine ⟨C,hC,?_⟩
  intro z hz
  have heq : completed c χ hmod hχ z = mellin f (z+(χ.k.natAbs:ℂ)/2) := by
    unfold completed
    dsimp [f]
    rw [mellin_div_const,(hP.hasMellin _).2]
  rw [heq]
  apply hb
  · simp only [add_re,div_ofNat_re,natCast_re]; linarith [hz.1]
  · simp only [add_re,div_ofNat_re,natCast_re]; linarith [hz.2]

theorem LFunction_exp_growth (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue)) (hk : χ.k ≠ 0) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖FamilyContinuation.LFunction χ z‖ ≤ A*Real.exp (B*|z.im|) := by
  have h := shifted_uncompleted_exp_bound (Real.pi*GaussianTheta.parameter c 1)
    (mul_pos Real.pi_pos (GaussianTheta.parameter_pos c 1 zero_lt_one)) χ.k.natAbs
    (completed c χ hmod hχ) (completed_strip_bounded c χ hmod hχ hk)
  obtain ⟨A,B,hA,hB,h⟩ := h
  refine ⟨A,B,hA,hB,?_⟩
  intro z hz
  rw [←primitive_eq_family c χ hmod hχ hk z]
  exact h z hz

end OAI.SevenEighths.Angular.PlainReflection
