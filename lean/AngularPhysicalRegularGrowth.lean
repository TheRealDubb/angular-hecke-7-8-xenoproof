import AngularPhysicalRegularInput
import AngularPlainUniformStrip

noncomputable section
open scoped Classical Topology
open Set Complex
namespace OAI.SevenEighths.Angular.PhysicalLogarithmic
open PhysicalLogarithmicInput ActualEisensteinCubic

theorem modulus_norm_ge_one (χ : AngularCharacter) : 1 ≤ (χ.modulus.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)

theorem regular_fixed_order_growth (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : AngularCharacter, χ.k.natAbs = n →
      FiniteFourier.IsPrimitiveOnIdeals χ.residue → ∀ z : ℂ, -(1/10:ℝ) ≤ z.re →
      ‖regular χ z‖ ≤ C*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|z.im|)^2 := by
  obtain ⟨C,hC,hgrowth⟩ := PlainReflection.primitive_upper_strip n
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨C+HeckeLogarithmicInput.uniformConstant+1,by positivity,?_⟩
  intro χ hn hp z hz
  by_cases hk : χ.k = 0
  · rw [regular_eq_typeZero χ hk]
    apply (HeckeLogarithmicInput.regular_right_growth
      (FiniteIdentification.toFinite χ hk) hp hz).trans
    change HeckeLogarithmicInput.uniformConstant*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*
      (3+|z.im|)^2 ≤ _
    gcongr
    linarith
  · rw [regular_eq_nonprincipal χ (Or.inl hk)]
    let c := ConcretePrimeRowBridge.idealGenerator χ.modulus
    letI : NeZero c := ⟨ConcretePrimeRowBridge.idealGenerator_ne_zero
      χ.modulus χ.modulus_ne_bot⟩
    have hmod : χ.modulus = Ideal.span {c} :=
      (ConcretePrimeRowBridge.span_idealGenerator χ.modulus).symm
    have htransport (M N : Ideal O) (he : M = N) (ρ : MulChar (O ⧸ M) ℂ)
        (hρ : FiniteFourier.IsPrimitiveOnIdeals ρ) :
        FiniteFourier.IsPrimitiveOnIdeals (he ▸ ρ) := by
      subst N
      exact hρ
    have h := hgrowth c χ hmod (htransport _ _ hmod χ.residue hp) hk hn z hz
    have he : HeckeStripActual.conductor c = (χ.modulus.absNorm:ℝ) := by
      simp only [HeckeStripActual.conductor,←hmod]
    rw [he] at h
    apply h.trans
    gcongr
    linarith

theorem regular_bounded_order_growth (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : AngularCharacter, χ.k.natAbs ≤ n →
      FiniteFourier.IsPrimitiveOnIdeals χ.residue → ∀ z : ℂ, -(1/10:ℝ) ≤ z.re →
      ‖regular χ z‖ ≤ C*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|z.im|)^2 := by
  induction n with
  | zero =>
      obtain ⟨C,hC,hgrowth⟩ := regular_fixed_order_growth 0
      exact ⟨C,hC,fun χ hn hp z hz => hgrowth χ (Nat.eq_zero_of_le_zero hn) hp z hz⟩
  | succ n ih =>
      obtain ⟨C,hC,hgrowth⟩ := ih
      obtain ⟨D,hD,hnew⟩ := regular_fixed_order_growth (n+1)
      refine ⟨C+D,by positivity,?_⟩
      intro χ hn hp z hz
      by_cases hold : χ.k.natAbs ≤ n
      · apply (hgrowth χ hold hp z hz).trans
        gcongr
        linarith
      · have he : χ.k.natAbs = n+1 := by omega
        apply (hnew χ he hp z hz).trans
        gcongr
        linarith

theorem regular_disk_growth (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : AngularCharacter, χ.k.natAbs ≤ n →
      FiniteFourier.IsPrimitiveOnIdeals χ.residue → ∀ a e t : ℝ,
      1/2 ≤ a → 0 ≤ e → ∀ z ∈ Metric.closedBall ((2:ℂ)+t*I) (2-a-2*e),
      ‖regular χ z‖ ≤ (4*C)*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|t|)^2 := by
  obtain ⟨C,hC,hgrowth⟩ := regular_bounded_order_growth n
  refine ⟨C,hC,?_⟩
  intro χ horder hp a e t ha he z hz
  have hn : ‖z-((2:ℂ)+t*I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2:ℂ)+t*I))
  have hi := Complex.abs_im_le_norm (z-((2:ℂ)+t*I))
  norm_num [Complex.sub_re,Complex.add_re,Complex.mul_re,
    Complex.sub_im,Complex.add_im,Complex.mul_im] at hr hi
  have hzre : -(1/10:ℝ) ≤ z.re := by
    have hh := neg_abs_le (z.re-2)
    linarith
  have hheight : 3+|z.im| ≤ 2*(3+|t|) := by
    have hab := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hab
    linarith [abs_nonneg t]
  have hsq : (3+|z.im|)^2 ≤ 4*(3+|t|)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|)
      (by positivity : 0 ≤ 2*(3+|t|))).mpr hheight
    nlinarith
  apply (hgrowth χ horder hp z hzre).trans
  calc
    _ ≤ C*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(4*(3+|t|)^2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

def complexity (χ : AngularCharacter) (t : ℝ) : ℝ :=
  2*(χ.modulus.absNorm:ℝ)*(3+|t|)^2

theorem complexity_ge_exp (χ : AngularCharacter) (t : ℝ) :
    Real.exp 1 ≤ complexity χ t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (modulus_norm_ge_one χ)

theorem exists_uniform_polynomial_exponent (n : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ χ : AngularCharacter, χ.k.natAbs ≤ n →
      FiniteFourier.IsPrimitiveOnIdeals χ.residue → ∀ a e t : ℝ,
      1/2 ≤ a → 0 < e → ∀ z ∈ Metric.ball ((2:ℂ)+t*I) (2-a-3*e),
      ‖regular χ z‖ ≤ (complexity χ t)^M := by
  obtain ⟨C,hC,hgrowth⟩ := regular_disk_growth n
  obtain ⟨M,hM,hb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := 2*C) (p := 1) (by norm_num)
  refine ⟨M,hM,?_⟩
  intro χ hn hp a e t ha he z hz
  have hz2 : z ∈ Metric.closedBall ((2:ℂ)+t*I) (2-a-2*e) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hz
  have hQ : (χ.modulus.absNorm:ℝ)^(3/5:ℝ) ≤ (χ.modulus.absNorm:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (modulus_norm_ge_one χ)
      (show (3/5:ℝ) ≤ 1 by norm_num)
  apply (hgrowth χ hn hp a e t ha he.le z hz2).trans
  calc
    _ ≤ (4*C)*(χ.modulus.absNorm:ℝ)*(3+|t|)^2 := by gcongr
    _ = (2*C)*complexity χ t := by unfold complexity; ring
    _ ≤ _ := by simpa only [Real.rpow_one] using hb _ (complexity_ge_exp χ t)

end OAI.SevenEighths.Angular.PhysicalLogarithmic

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.modulus_norm_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.modulus_norm_ge_one

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.regular_fixed_order_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.regular_fixed_order_growth

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.regular_bounded_order_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.regular_bounded_order_growth

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.regular_disk_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.regular_disk_growth

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.complexity_ge_exp
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.complexity_ge_exp

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmic.exists_uniform_polynomial_exponent
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmic.exists_uniform_polynomial_exponent
