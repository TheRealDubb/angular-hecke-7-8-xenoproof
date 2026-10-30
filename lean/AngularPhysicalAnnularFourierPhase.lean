import AngularPhysicalAnnularFourierRay

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularFourier
open EisensteinSchwartzPoisson AnnularSchwartz

theorem annular_unit_mul (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (u z:ℂ) (hu:‖u‖=1) :
    annularCLM k a b ha W (u*z)=u^k*annularCLM k a b ha W z := by
  rw [annularCLM_apply k a b ha W hs,annularCLM_apply k a b ha W hs,norm_mul,hu,one_mul]
  rw [mul_div_assoc,mul_zpow]
  ring

theorem paperFourier_const_mul (f:ℂ→ℂ) (c u:ℂ) :
    paperFourier (fun z=>c*f z) u=c*paperFourier f u := by
  have he:(fun z:ℂ=>paperE (-(z*u))*(c*f z))=fun z=>c*(paperE (-(z*u))*f z) := by
    funext z
    ring
  unfold paperFourier
  rw [he,integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem annular_fourier_unit_mul (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (v u:ℂ) (hv:‖v‖=1) :
    paperFourier (annularCLM k a b ha W) (v*u)=
      v^(-k)*paperFourier (annularCLM k a b ha W) u := by
  have hv0:v≠0:=by intro hz; simp [hz] at hv
  have hp:v^k≠0:=zpow_ne_zero _ hv0
  have he:(fun z:ℂ=>annularCLM k a b ha W (v*z))=
      fun z=>v^k*annularCLM k a b ha W z :=
    funext (fun z=>annular_unit_mul k a b ha W hs v z hv)
  have hh:=paperFourier_comp_mul (annularCLM k a b ha W) v hv0 (v*u)
  rw [he,paperFourier_const_mul,hv,one_pow,div_one,one_smul,
    show v*u/v=u by field_simp] at hh
  calc
    _=(v^k)⁻¹*(v^k*paperFourier (annularCLM k a b ha W) (v*u)) := by
      rw [←mul_assoc,inv_mul_cancel₀ hp,one_mul]
    _=_ := by rw [hh,zpow_neg]

theorem actual_angular_fourier (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (u:ℂ) (hu:u≠0) :
    paperFourier (annularCLM k a b ha W) u=
      (u/(‖u‖:ℂ))^(-k)*profile k a b ha W (‖u‖^2) := by
  have hn:‖u‖≠0:=norm_ne_zero_iff.mpr hu
  have hnC:(‖u‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hn
  have hv:‖u/(‖u‖:ℂ)‖=1:=by simp [norm_div,hn]
  have he:(u/(‖u‖:ℂ))*(‖u‖:ℂ)=u:=div_mul_cancel₀ _ hnC
  calc
    _=paperFourier (annularCLM k a b ha W) ((u/(‖u‖:ℂ))*(‖u‖:ℂ)) := congrArg _ he.symm
    _=(u/(‖u‖:ℂ))^(-k)*paperFourier (annularCLM k a b ha W) (‖u‖:ℂ) :=
      annular_fourier_unit_mul k a b ha W hs _ _ hv
    _=_ := by rw [profile_eq_paper,Real.sqrt_sq (norm_nonneg u)]

theorem exists_unit_antiphase (k:ℤ) (hk:k≠0) :
    ∃v:ℂ,‖v‖=1 ∧ v^k=(-1:ℂ) := by
  let θ:ℝ:=Real.pi/(k:ℝ)
  let v:ℂ:=Complex.exp ((θ:ℂ)*Complex.I)
  refine ⟨v,Complex.norm_exp_ofReal_mul_I θ,?_⟩
  have hkC:(k:ℂ)≠0:=Int.cast_ne_zero.mpr hk
  have he:(k:ℂ)*((θ:ℂ)*Complex.I)=(Real.pi:ℂ)*Complex.I := by
    dsimp [θ]
    push_cast
    field_simp
  change Complex.exp ((θ:ℂ)*Complex.I)^k=(-1:ℂ)
  rw [←Complex.exp_int_mul,he,Complex.exp_pi_mul_I]

theorem nonzero_order_fourier_zero (k:ℤ) (hk:k≠0) (a b:ℝ) (ha:0<a)
    (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) :
    paperFourier (annularCLM k a b ha W) 0=0 := by
  obtain ⟨v,hv,hpow⟩:=exists_unit_antiphase k hk
  have hh:=annular_fourier_unit_mul k a b ha W hs v 0 hv
  simp only [mul_zero,zpow_neg,hpow,inv_neg,inv_one,neg_one_mul] at hh
  linear_combination (1/2:ℂ)*hh

end OAI.SevenEighths.Angular.AnnularFourier

#print axioms OAI.SevenEighths.Angular.AnnularFourier.actual_angular_fourier
#print axioms OAI.SevenEighths.Angular.AnnularFourier.nonzero_order_fourier_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularFourier.nonzero_order_fourier_zero
