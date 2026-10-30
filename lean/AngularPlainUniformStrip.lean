import AngularRightSeriesBounds
import AngularPlainGrowth
import AngularImprimitiveReflection

/-! Actual angular polynomial growth from the proved shifted theta growth and
the generic strip principle. No finite-family zero supremum is imported. -/
noncomputable section
open scoped Classical Topology
open Set Complex
namespace OAI.SevenEighths.Angular.PlainReflection
open ActualEisensteinCubic FamilyContinuation HeckeStripActual PrimitiveReduction
open HeckeDeletionBounds

theorem primitive_uniform_strip (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (c : O) [NeZero c] (χ : AngularCharacter)
      (hmod : χ.modulus = Ideal.span {c})
      (_hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue)),
      χ.k ≠ 0 → χ.k.natAbs = n → ∀ z ∈ HeckeStrip.closedStrip,
      ‖LFunction χ z‖ ≤ C*(conductor c)^(3/5:ℝ)*(3+|z.im|)^2 := by
  obtain ⟨Cg,hCg,hreflect⟩ := primitive_reflected_bound n
  let D := HeckeReciprocalBound.bound (11/10)
  have hD : 0 ≤ D := tsum_nonneg (fun _ => norm_nonneg _)
  let C := (1+Cg)*D+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨36*C,by positivity,?_⟩
  intro c _ χ hmod hχ hk hn z hz
  have hq0 : 0 ≤ conductor c := le_trans zero_le_one (conductor_ge_one c)
  apply HeckeStrip.uniform_strip_bound (conductor c) C (conductor_ge_one c) hC.le
    (LFunction χ) (LFunction_differentiable χ hk).diffContOnCl
    (LFunction_exp_growth c χ hmod hχ hk) ?_ ?_ z hz
  · intro w hw
    have h := hreflect c χ hmod hχ hk hn w (by rw [hw]) (by rw [hw]; norm_num)
    have hd : ‖LFunction χ.conjugate (1-w)‖ ≤ D :=
      LFunction_norm_le χ.conjugate (by norm_num : (1:ℝ)<11/10) (by norm_num [hw])
    have he : 1/2-w.re = 3/5 := by rw [hw]; norm_num
    rw [he] at h
    have hCD : Cg*D ≤ C := by dsimp [C]; nlinarith
    calc
      _ ≤ Cg*(conductor c)^(3/5:ℝ)*(3+|w.im|)^2 *
          ‖LFunction χ.conjugate (1-w)‖ := h
      _ ≤ Cg*(conductor c)^(3/5:ℝ)*(3+|w.im|)^2*D := by gcongr
      _ = (Cg*D)*(conductor c)^(3/5:ℝ)*(3+|w.im|)^2 := by ring
      _ ≤ _ := by gcongr
  · intro w hw
    apply (LFunction_norm_le χ (by norm_num : (1:ℝ)<11/10) hw.ge).trans
    change D ≤ C
    dsimp [C]
    nlinarith

theorem primitive_upper_strip (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (c : O) [NeZero c] (χ : AngularCharacter)
      (hmod : χ.modulus = Ideal.span {c})
      (_hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue)),
      χ.k ≠ 0 → χ.k.natAbs = n → ∀ s : ℂ, -(1/10:ℝ) ≤ s.re →
      ‖LFunction χ s‖ ≤ C*(conductor c)^(3/5:ℝ)*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hstrip⟩ := primitive_uniform_strip n
  let D := HeckeReciprocalBound.bound (11/10)
  have hD : 0 ≤ D := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C+D,by positivity,?_⟩
  intro c _ χ hmod hχ hk hn s hs
  have hq0 : 0 ≤ conductor c := le_trans zero_le_one (conductor_ge_one c)
  by_cases hr : s.re ≤ 11/10
  · apply (hstrip c χ hmod hχ hk hn s ⟨hs,hr⟩).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD)
        (Real.rpow_nonneg hq0 _)) (sq_nonneg _)
  · have hd : ‖LFunction χ s‖ ≤ D :=
      LFunction_norm_le χ (by norm_num : (1:ℝ)<11/10) (le_of_not_ge hr)
    have hq : 1 ≤ (conductor c)^(3/5:ℝ) :=
      Real.one_le_rpow (conductor_ge_one c) (by norm_num)
    have hh : 1 ≤ (3+|s.im|)^2 := by nlinarith [abs_nonneg s.im]
    calc
      _ ≤ D := hd
      _ ≤ C+D := by linarith
      _ ≤ (C+D)*(conductor c)^(3/5:ℝ) := le_mul_of_one_le_right (by positivity) hq
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hh

theorem original_upper_strip (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : AngularCharacter,
      χ.k ≠ 0 → χ.k.natAbs = n → ∀ s : ℂ, -(1/10:ℝ) ≤ s.re →
      ‖LFunction χ s‖ ≤ C*(χ.modulus.absNorm:ℝ)^(3/5:ℝ) *
        ((radical χ.modulus).absNorm:ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨Cg,hCg,hgrowth⟩ := primitive_upper_strip n
  obtain ⟨Cd,hCd,hdel⟩ := DeletionBounds.factors_any_re_subpower_bound ε hε
  refine ⟨Cg*Cd,by positivity,?_⟩
  intro χ hk hn s hs
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  have hq0 : 0 ≤ conductor (generator χ) := le_trans zero_le_one (conductor_ge_one _)
  have hg := hgrowth (generator χ) (primitive χ) rfl (primitive_isPrimitive χ) hk hn s hs
  have hQ : (conductor (generator χ))^(3/5:ℝ) ≤ (χ.modulus.absNorm:ℝ)^(3/5:ℝ) := by
    change ((primitive χ).modulus.absNorm:ℝ)^(3/5:ℝ) ≤ _
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast PrimitiveReduction.norm_le χ) (by norm_num)
  have hR : 1 ≤ ((radical χ.modulus).absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hd : ‖factors χ s‖ ≤ Cd*((radical χ.modulus).absNorm:ℝ)^(1/10+ε) := by
    apply (hdel χ.modulus (primitive χ) s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hm : max (-s.re) 0 ≤ 1/10 := max_le (by linarith) (by norm_num)
    linarith
  rw [FamilyContinuation.LFunction,primitiveL_eq_family_primitive χ hk,norm_mul]
  calc
    _ ≤ (Cg*(conductor (generator χ))^(3/5:ℝ)*(3+|s.im|)^2) *
        (Cd*((radical χ.modulus).absNorm:ℝ)^(1/10+ε)) :=
      mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ (Cg*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2) *
        (Cd*((radical χ.modulus).absNorm:ℝ)^(1/10+ε)) := by gcongr
    _ = _ := by ring

end OAI.SevenEighths.Angular.PlainReflection
