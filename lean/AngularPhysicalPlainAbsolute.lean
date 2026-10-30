import AngularPhysicalFinite
import OAI.NumberTheory.DirichletL.Moments.Counting
import OAI.NumberTheory.DirichletL.Moments.PrimeSlot

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainAbsolute
open OAI.SevenEighths.Angular.Dyadic
local notation "O" => ActualEisensteinCubic.O

theorem plain_all_ideals (χ : AngularCharacter) (W : ℝ → ℂ) (D σ t : ℝ) :
    polynomial χ false W D σ t = (D : ℂ)^(-(1/2 : ℂ))*
      ∑' I : Ideal O, χ.idealHom I * W ((I.absNorm : ℝ)/D)*
        (((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ t) := by
  unfold polynomial
  congr 1
  let f : Ideal O → ℂ := fun I => χ.idealHom I * W ((I.absNorm : ℝ)/D)*
    (((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ t)
  have hf : Function.support f ⊆ {I : Ideal O | I ≠ 0} := by
    intro I hi hz
    subst I
    exact hi (by simp only [f, map_zero, zero_mul])
  have he := tsum_subtype_eq_of_support_subset hf
  calc
    _ = ∑' I : {I : Ideal O // I ≠ 0}, f I.val := by
      apply tsum_congr
      intro I
      simp only [summand, coefficient, Bool.false_eq_true, ite_false, Dyadic.norm, f]
    _ = _ := he

theorem polynomial_absolute (χ : AngularCharacter) (W : ℝ → ℂ) (b B D freq : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hD : 0 < D)
    (hbound : ∀ x, ‖W x‖ ≤ B) (hs : ∀ x, W x ≠ 0 → x ≤ b) :
    ‖polynomial χ false W D 0 freq‖ ≤ (128*b*B)*Real.sqrt D := by
  let f : Ideal O → ℂ := fun I => χ.idealHom I * W ((I.absNorm : ℝ)/D)*
    (((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift 0 freq)
  have hzero : f 0 = 0 := by simp only [f, map_zero, zero_mul]
  have hbnd (I : Ideal O) : ‖f I‖ ≤ B := by
    by_cases hz : I = 0
    · simpa only [hz, hzero, norm_zero] using hB
    have hI : 0 < (I.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)
    dsimp only [f]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hI hD)]
    simp only [Complex.neg_re, shift_re, neg_zero, Real.rpow_zero, mul_one]
    exact (mul_le_mul (χ.norm_idealHom_le_one I) (hbound _) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul B)
  have hsupp (I : Ideal O) (hi : f I ≠ 0) : (I.absNorm : ℝ) ≤ b*D := by
    have hw : W ((I.absNorm : ℝ)/D) ≠ 0 := by
      intro hz
      exact hi (by simp only [f, hz, mul_zero, zero_mul])
    exact (div_le_iff₀ hD).mp (hs _ hw)
  have hh := CenteredMomentCounting.norm_tsum_ideal_ball f (b*D) B
    (mul_nonneg hb hD.le) hB hzero hbnd hsupp
  rw [plain_all_ideals, ←CenteredMomentPrimeSlot.sqrt_inverse_cpow D hD, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
  have hsq : Real.sqrt D * Real.sqrt D = D := by rw [←pow_two, Real.sq_sqrt hD.le]
  have hroot : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  calc
    _ = (128*b*B)*((Real.sqrt D)⁻¹*(Real.sqrt D*Real.sqrt D)) := by rw [hsq]; ring
    _ = _ := by rw [inv_mul_cancel_left₀ hroot]

theorem small_polynomial (χ : AngularCharacter) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (_ha : 0 < a)
    (hWs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b)
    (D freq : ℝ) (hD : 0 < D) (hD1 : D ≤ 1) :
    ‖polynomial χ false W D 0 freq‖ ≤ (128*max 0 b)*(SchwartzMap.seminorm ℝ 0 0 W) := by
  have hh := polynomial_absolute χ W (max 0 b) (SchwartzMap.seminorm ℝ 0 0 W) D freq
    (le_max_left _ _) (apply_nonneg _ _) hD
    (fun x => SchwartzMap.norm_le_seminorm ℝ W x)
    (fun x hx => (hWs hx).2.trans (le_max_right _ _))
  exact hh.trans (mul_le_of_le_one_right (by positivity) ((Real.sqrt_le_one).mpr hD1))

#print axioms polynomial_absolute
#print axioms small_polynomial
end OAI.SevenEighths.Angular.PlainAbsolute
