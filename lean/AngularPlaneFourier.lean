import OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
import OAI.NumberTheory.DirichletL.Moments.Lattice

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform
namespace OAI.SevenEighths.Angular.PlaneVolume
open EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def fourierControl (f : 𝓢(ℂ,ℂ)) : ℝ :=
  (2/Real.sqrt 3)*2^4*(Finset.Iic (4,0)).sup (schwartzSeminormFamily ℝ ℂ ℂ) (𝓕 f)

theorem fourierControl_nonneg (f : 𝓢(ℂ,ℂ)) : 0 ≤ fourierControl f := by
  unfold fourierControl
  positivity

theorem fourier_weighted (f : 𝓢(ℂ,ℂ)) (u : ℂ) :
    (1+‖u‖^2)^2*‖paperFourier f u‖ ≤ fourierControl f := by
  let ξ := paperFrequency u
  have hn : ‖ξ‖^2=(4/3:ℝ)*‖u‖^2 := paperFrequency_norm_sq u
  have hpow : (1+‖u‖^2)^2 ≤ (1+‖ξ‖)^4 := by
    have hb : 1+‖u‖^2 ≤ (1+‖ξ‖)^2 := by nlinarith [norm_nonneg ξ]
    have hh := pow_le_pow_left₀ (by positivity : 0≤1+‖u‖^2) hb 2
    simpa only [←pow_mul] using hh
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (4,0)) (k := 4) (n := 0) le_rfl le_rfl (𝓕 f) ξ
  simp only [norm_iteratedFDeriv_zero] at hb
  rw [paperFourier_eq_standard,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤2/Real.sqrt 3)]
  change (1+‖u‖^2)^2*((2/Real.sqrt 3)*‖(𝓕 f) ξ‖) ≤ _
  calc
    _ = (2/Real.sqrt 3)*((1+‖u‖^2)^2*‖(𝓕 f) ξ‖) := by ring
    _ ≤ (2/Real.sqrt 3)*((1+‖ξ‖)^4*‖(𝓕 f) ξ‖) := by gcongr
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by
        unfold fourierControl schwartzSeminormFamily
        ring)

theorem plane_lattice_summable (f : 𝓢(ℂ,ℂ)) (a : ℂ) (ha : a≠0) :
    Summable (fun h : O => ‖paperFourier f (a*eisEmbedding h)‖) := by
  have ht : 0<‖a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _
    ((scaled_eisenstein_cauchy_summable (‖a‖^2) ht).mul_left (fourierControl f))
  intro h
  rw [←div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  have hh := fourier_weighted f (a*eisEmbedding h)
  simpa only [norm_mul,mul_pow,mul_comm] using hh

theorem plane_nonzero_lattice_bound (f : 𝓢(ℂ,ℂ)) (a : ℂ) (ha : a≠0) :
    ‖a‖^2*(∑' h : {h : O // h≠0}, ‖paperFourier f (a*eisEmbedding h.val)‖) ≤
      nonzeroLatticeEnvelopeConstant*fourierControl f := by
  apply (nonzero_lattice_envelope_sum (‖a‖^2) (fourierControl f)
    (sq_pos_of_pos (norm_pos_iff.mpr ha)) (fourierControl_nonneg f)
    (fun h=>‖paperFourier f (a*eisEmbedding h.val)‖) (fun _=>norm_nonneg _) ?_).2
  intro h
  simpa only [norm_mul,mul_pow] using fourier_weighted f (a*eisEmbedding h.val)

theorem plane_source_control (T : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℂ,ℂ)) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧ ∀ W,
      fourierControl (T W) ≤ C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨S,C,hC,hb⟩ := schwartzCLM_finite_seminorm_control
    ((FourierTransform.fourierCLM ℝ 𝓢(ℂ,ℂ)).comp T) (Finset.Iic (4,0))
  refine ⟨S,(2/Real.sqrt 3)*2^4*C,by positivity,?_⟩
  intro W
  exact (mul_le_mul_of_nonneg_left (hb W) (by positivity : 0≤(2/Real.sqrt 3)*2^4)).trans_eq
    (by ring)

end OAI.SevenEighths.Angular.PlaneVolume
