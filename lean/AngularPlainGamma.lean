import OAI.NumberTheory.DirichletL.Hecke.DyadicReflection

/-! The actual half-degree gamma shift for a fixed angular type. Constants may
depend on the angular order, while the polynomial height degree is two. -/
noncomputable section
open scoped Classical Topology BigOperators
open Set Complex

namespace OAI.SevenEighths.Angular.PlainReflection

theorem gamma_real_ratio_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ x ∈ Icc (-(1/10 : ℝ)) (1/2),
      Real.Gamma (1-x+n/2) / Real.Gamma (x+n/2+2) ≤ C := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcont : ContinuousOn (fun x : ℝ =>
      Real.Gamma (1-x+n/2) / Real.Gamma (x+n/2+2))
      (Icc (-(1/10 : ℝ)) (1/2)) := by
    intro x hx
    have hnum : DifferentiableAt ℝ Real.Gamma (1-x+n/2) :=
      Real.differentiableAt_Gamma (by intro m hm; have := Nat.cast_nonneg (α:=ℝ) m; linarith [hx.2])
    have hden : DifferentiableAt ℝ Real.Gamma (x+n/2+2) :=
      Real.differentiableAt_Gamma (by intro m hm; have := Nat.cast_nonneg (α:=ℝ) m; linarith [hx.1])
    exact ((hnum.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => 1-y+n/2)
      (show ContinuousAt (fun y : ℝ => 1-y+n/2) x by fun_prop)).div
      (hden.continuousAt.comp (g := Real.Gamma) (f := fun y : ℝ => y+n/2+2)
        (show ContinuousAt (fun y : ℝ => y+n/2+2) x by fun_prop))
      (Real.Gamma_pos_of_pos (show 0<x+n/2+2 by linarith [hx.1])).ne').continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))

theorem gamma_ratio_strip_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
    -(1/10 : ℝ) ≤ s.re → s.re ≤ 1/2 →
    ‖Complex.Gamma (1-s+n/2) / Complex.Gamma (s+n/2)‖ ≤
      C*(3+n/2+|s.im|)^2 := by
  obtain ⟨C,hC,hreal⟩ := gamma_real_ratio_bound n
  refine ⟨C,hC,?_⟩
  intro s hl hr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (n/2+1/2) (1/2-s.re) (-s.im) 2 (by linarith) (by norm_num; linarith)
  have hnum : ((n/2+1/2 : ℝ) : ℂ)+((1/2-s.re : ℝ)+(-s.im)*I)=1-s+n/2 := by
    apply Complex.ext <;> simp <;> ring
  have hden : ((n/2+1/2 : ℝ) : ℂ)-((1/2-s.re : ℝ)+(-s.im)*I)+(2 : ℕ)=s+n/2+2 := by
    apply Complex.ext <;> simp <;> ring
  simp only [ofReal_neg] at hb
  rw [hnum,hden] at hb
  have hb' : ‖Complex.Gamma (1-s+n/2) / Complex.Gamma (s+n/2+2)‖ ≤ C := by
    apply hb.trans
    convert hreal s.re ⟨hl,hr⟩ using 1 <;> congr 1 <;> ring_nf
  have heq : Complex.Gamma (1-s+n/2) / Complex.Gamma (s+n/2) =
      (∏ k ∈ Finset.range 2, (s+n/2+k)) *
        (Complex.Gamma (1-s+n/2) / Complex.Gamma (s+n/2+2)) := by
    rw [div_eq_mul_inv,CubicReflectionKernel.inverse_Gamma_shift (s+n/2) 2]
    simp only [Nat.cast_ofNat,div_eq_mul_inv]
    ring
  have hs : ‖s+n/2‖ ≤ 1+n/2+|s.im| := by
    have hsr : |(s+(n:ℂ)/2).re| ≤ 1+n/2 := abs_le.mpr ⟨by simp; linarith,by simp; linarith⟩
    have hh := Complex.norm_le_abs_re_add_abs_im (s+(n:ℂ)/2)
    simp only [add_im,div_ofNat_im,natCast_im,zero_div,add_zero] at hh
    linarith
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor (s+n/2) 2
  norm_num only [Nat.cast_ofNat] at hf
  have hf' : ‖∏ k ∈ Finset.range 2,(s+n/2+k)‖ ≤ (3+n/2+|s.im|)^2 :=
    hf.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  rw [heq,norm_mul]
  exact (mul_le_mul hf' hb' (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_fixed_degree (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
    -(1/10 : ℝ) ≤ s.re → s.re ≤ 1/2 →
    ‖Complex.Gamma (1-s+n/2) / Complex.Gamma (s+n/2)‖ ≤ C*(3+|s.im|)^2 := by
  obtain ⟨C,hC,h⟩ := gamma_ratio_strip_bound n
  refine ⟨C*(1+(n:ℝ)/2)^2,by positivity,?_⟩
  intro s hl hr
  have hh : 3+(n:ℝ)/2+|s.im| ≤ (1+(n:ℝ)/2)*(3+|s.im|) := by
    have := mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (abs_nonneg s.im)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  calc
    _ ≤ C*(3+(n:ℝ)/2+|s.im|)^2 := h s hl hr
    _ ≤ C*((1+(n:ℝ)/2)*(3+|s.im|))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) hC.le
    _ = _ := by ring

end OAI.SevenEighths.Angular.PlainReflection
