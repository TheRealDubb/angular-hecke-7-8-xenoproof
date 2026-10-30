import AngularPhysicalAnnularFourierPhase
import OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularFourier
open EisensteinSchwartzPoisson AnnularSchwartz ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem norm_fourier_eq_profile (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (u:ℂ) :
    ‖paperFourier (annularCLM k a b ha W) u‖=‖profile k a b ha W (‖u‖^2)‖ := by
  by_cases hu:u=0
  · subst u
    rw [profile_eq_paper]
    simp
  rw [actual_angular_fourier k a b ha W hs u hu,norm_mul,norm_zpow]
  have hn:‖u/(‖u‖:ℂ)‖=1:=by simp [norm_div,hu]
  rw [hn,one_zpow,one_mul]

theorem profile_lattice_summable (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (X:ℝ) (hX:0<X) :
    Summable (fun z:O=>‖profile k a b ha W (‖eisEmbedding z‖^2/X)‖) := by
  have hh:=PlaneVolume.plane_lattice_summable (annularCLM k a b ha W)
    (Real.sqrt X:ℂ)⁻¹ (inverseSqrt_ne_zero X hX)
  apply hh.congr
  intro z
  rw [norm_fourier_eq_profile k a b ha W hs]
  congr 2
  rw [norm_mul,mul_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg X),inv_pow,Real.sq_sqrt hX.le]
  ring

theorem profile_decayTwo (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) :
    CenteredMomentReflectionDeletion.DecayTwo (profile k a b ha W) := by
  obtain ⟨S,C,hC,hb⟩:=profile_euler_weighted_bound k a b ha 2 0
  refine ⟨C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,by positivity,?_⟩
  intro x hx
  have hh:=hb W 0 le_rfl x hx.le
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
  exact (mul_le_mul_of_nonneg_right (show x^2≤(1+x)^2 by nlinarith)
    (norm_nonneg _)).trans hh

end OAI.SevenEighths.Angular.AnnularFourier

#print axioms OAI.SevenEighths.Angular.AnnularFourier.profile_lattice_summable
#print axioms OAI.SevenEighths.Angular.AnnularFourier.profile_decayTwo
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularFourier.profile_decayTwo
