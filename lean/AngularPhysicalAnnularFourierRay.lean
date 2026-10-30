import AngularAnnularSchwartz
import OAI.NumberTheory.DirichletL.Poisson.RadialFourier

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularFourier
open EisensteinSchwartzPoisson AnnularSchwartz

def fourierCLM (k:ℤ) (a b:ℝ) (ha:0<a) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℂ,ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(ℂ,ℂ)).comp (annularCLM k a b ha)

def rayCLM (k:ℤ) (a b:ℝ) (ha:0<a) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (2/Real.sqrt 3:ℝ) • (paperRealRayCLM.comp (fourierCLM k a b ha))

def profile (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (x:ℝ) : ℂ :=
  rayCLM k a b ha W (Real.sqrt x)

theorem profile_eq_paper (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (x:ℝ) :
    profile k a b ha W x=paperFourier (annularCLM k a b ha W) (Real.sqrt x:ℂ) := by
  rw [paperFourier_eq_standard]
  rfl

def eulerCLM (k:ℤ) (a b:ℝ) (ha:0<a) (j:ℕ) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (halfEulerIterateCLM j).comp (rayCLM k a b ha)

theorem profile_euler (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (j:ℕ)
    (x:ℝ) (hx:0≤x) :
    LocalLogFourier.eulerDeriv (profile k a b ha W) j x=eulerCLM k a b ha j W (Real.sqrt x) := by
  change LocalLogFourier.eulerDeriv (fun y=>rayCLM k a b ha W (Real.sqrt y)) j x=_
  rw [eulerDeriv_sqrt_profile _ j x hx]
  simp only [eulerCLM,ContinuousLinearMap.comp_apply,halfEulerIterateCLM_apply]

theorem profile_contDiffOn (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) :
    ContDiffOn ℝ ∞ (profile k a b ha W) (Set.Ioi 0) :=
  contDiffOn_sqrt_profile _

theorem profile_log_contDiff (k:ℤ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (x:ℝ) (hx:0≤x) :
    ContDiff ℝ ∞ (fun t:ℝ=>profile k a b ha W (x*Real.exp t)) :=
  contDiff_sqrt_profile_log _ x hx

theorem profile_euler_weighted_bound (k:ℤ) (a b:ℝ) (ha:0<a) (A J:ℕ) :
    ∃(S:Finset (ℕ×ℕ))(C:ℝ),0<C ∧ ∀(W:𝓢(ℝ,ℂ))(j:ℕ),j≤J →
      ∀(x:ℝ),0≤x → (1+x)^A*‖LocalLogFourier.eulerDeriv (profile k a b ha W) j x‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨S,C,hC,hbound⟩:=schwartzCLM_family_finite_seminorm_control (eulerCLM k a b ha) A J
  refine ⟨S,2^A*C,by positivity,?_⟩
  intro W j hj x hx
  rw [profile_euler k a b ha W j x hx]
  apply (sqrt_profile_rapid_bound _ A x hx).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W j hj) (show 0≤(2:ℝ)^A by positivity)

theorem profile_decay (k:ℤ) (a b:ℝ) (ha:0<a) (A:ℕ) :
    ∃(S:Finset (ℕ×ℕ))(C:ℝ),0<C ∧ ∀(W:𝓢(ℝ,ℂ))(x:ℝ),0≤x →
      ‖profile k a b ha W x‖≤(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/(1+x)^A := by
  obtain ⟨S,C,hC,hb⟩:=profile_euler_weighted_bound k a b ha A 0
  refine ⟨S,C,hC,?_⟩
  intro W x hx
  apply (le_div_iff₀ (by positivity : 0<(1+x)^A)).mpr
  simpa [LocalLogFourier.eulerDeriv,mul_comm] using hb W 0 le_rfl x hx

end OAI.SevenEighths.Angular.AnnularFourier

#print axioms OAI.SevenEighths.Angular.AnnularFourier.profile_euler_weighted_bound
#print axioms OAI.SevenEighths.Angular.AnnularFourier.profile_decay
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularFourier.profile_decay
