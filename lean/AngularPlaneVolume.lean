import AngularPlaneFourier

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform
namespace OAI.SevenEighths.Angular.PlaneVolume
open EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem plane_zero_mode_error (f : 𝓢(ℂ,ℂ)) (a : ℂ) (ha : a≠0)
    (A : O → ℂ) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ h, ‖A h‖ ≤ B) :
    ‖(‖a‖^2) • (∑' h : O, A h * paperFourier f (a*eisEmbedding h)) -
      (‖a‖^2) • (A 0 * paperFourier f 0)‖ ≤ B * (nonzeroLatticeEnvelopeConstant*fourierControl f) := by
  let t := ‖a‖^2
  have ht : 0<t := sq_pos_of_pos (norm_pos_iff.mpr ha)
  let F : O → ℂ := fun h => A h * paperFourier f (a*eisEmbedding h)
  have hs := plane_lattice_summable f a ha
  have hF (h : O) : ‖F h‖ ≤ B * ‖paperFourier f (a*eisEmbedding h)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA h) (norm_nonneg _)
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF (hs.mul_left B)
  have hsplit := hFs.of_norm.tsum_eq_add_tsum_ite 0
  have hzero : F 0 = A 0 * paperFourier f 0 := by simp only [F, map_zero, mul_zero]
  have htail : (∑' h : O, if h = 0 then 0 else F h) =
      ∑' h : {h : O // h ≠ 0}, F h := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  have heq : (∑' h : O, F h) - F 0 = ∑' h : {h : O // h ≠ 0}, F h := by
    rw [hsplit, htail]
    ring
  have hn : ‖∑' h : {h : O // h ≠ 0}, F h‖ ≤
      B * (∑' h : {h : O // h ≠ 0},
        ‖paperFourier f (a*eisEmbedding h.val)‖) := by
    calc
      _ ≤ ∑' h : {h : O // h ≠ 0}, ‖F h‖ := norm_tsum_le_tsum_norm (hFs.subtype _)
      _ ≤ ∑' h : {h : O // h ≠ 0}, B *
          ‖paperFourier f (a*eisEmbedding h.val)‖ :=
        (hFs.subtype _).tsum_le_tsum (fun h => hF h) ((hs.subtype _).mul_left B)
      _ = _ := tsum_mul_left
  change ‖t • (∑' h : O, F h) - t • (A 0 * paperFourier f 0)‖ ≤ _
  rw [← hzero, ← smul_sub, heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ t * (B * ∑' h : {h : O // h ≠ 0},
        ‖paperFourier f (a*eisEmbedding h.val)‖) :=
      mul_le_mul_of_nonneg_left hn ht.le
    _ = B * (t * ∑' h : {h : O // h ≠ 0},
        ‖paperFourier f (a*eisEmbedding h.val)‖) := by ring
    _ ≤ B * (nonzeroLatticeEnvelopeConstant*fourierControl f) := mul_le_mul_of_nonneg_left (plane_nonzero_lattice_bound f a ha) hB


def scaledPlane (f : 𝓢(ℂ,ℂ)) (X : ℝ) (hX : 0<X) : 𝓢(ℂ,ℂ) :=
  affinePullback f (complexMulEquiv ((Real.sqrt X:ℂ)⁻¹) (inverseSqrt_ne_zero X hX)) 0

theorem scaledPlane_apply (f : 𝓢(ℂ,ℂ)) (X : ℝ) (hX : 0<X) (z : ℂ) :
    scaledPlane f X hX z=f (z/(Real.sqrt X:ℂ)) := by
  simp only [scaledPlane,affinePullback_apply,complexMulEquiv_apply,add_zero,div_eq_mul_inv,mul_comm]

theorem scaledPlane_fourier (f : 𝓢(ℂ,ℂ)) (X : ℝ) (hX : 0<X) (u : ℂ) :
    paperFourier (scaledPlane f X hX) u=X • paperFourier f ((Real.sqrt X:ℂ)*u) := by
  have hf : (scaledPlane f X hX : ℂ→ℂ)=fun z=>f ((Real.sqrt X:ℂ)⁻¹*z) := by
    funext z
    simp only [scaledPlane,affinePullback_apply,complexMulEquiv_apply,add_zero]
  rw [hf,paperFourier_comp_mul f _ (inverseSqrt_ne_zero X hX),inverseSqrt_norm_sq X hX]
  simp only [one_div_one_div,div_inv_eq_mul,mul_comm]

theorem periodic_plane_volume_error (f : 𝓢(ℂ,ℂ)) (X : ℝ) (hX : 0<X)
    (c : O) (hc : c≠0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z)*f (eisEmbedding z/(Real.sqrt X:ℂ))) -
      (X/‖eisEmbedding c‖^2:ℝ) • ((∑ r : O ⧸ Ideal.span {c},P r)*paperFourier f 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c},‖P r‖)*(nonzeroLatticeEnvelopeConstant*fourierControl f) := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h=>∑ r : O ⧸ Ideal.span {c},P r*ψ (Ideal.Quotient.mk (Ideal.span {c}) h*r)
  let a : ℂ := (Real.sqrt X:ℂ)/eisEmbedding c
  have ha : a≠0 := div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne')
    (eisEmbedding_ne_zero hc)
  have hn : ‖a‖^2=X/‖eisEmbedding c‖^2 := by
    simp only [a,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg X),Real.sq_sqrt hX.le]
  have hA (h : O) : ‖A h‖≤∑ r : O ⧸ Ideal.span {c},‖P r‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro r _
    rw [norm_mul]
    have hψ : ‖ψ (Ideal.Quotient.mk (Ideal.span {c}) h*r)‖=1 := by
      exact ψ.norm_apply _
    rw [hψ,mul_one]
  have hz : A 0=∑ r : O ⧸ Ideal.span {c},P r := by simp [A]
  have h := plane_zero_mode_error f a ha A (∑ r : O ⧸ Ideal.span {c},‖P r‖)
    (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hA
  rw [hn,hz] at h
  have hp := actual_eisenstein_paper_poisson_trace (scaledPlane f X hX) c hc P
  change (∑' z : O,P (Ideal.Quotient.mk (Ideal.span {c}) z)*scaledPlane f X hX (eisEmbedding z))=
    (1/‖eisEmbedding c‖^2:ℝ) • ∑' h : O,A h*paperFourier (scaledPlane f X hX)
      (eisEmbedding h/eisEmbedding c) at hp
  simp only [scaledPlane_apply,scaledPlane_fourier,mul_smul_comm,tsum_const_smul'',smul_smul] at hp
  have hscale : (1/‖eisEmbedding c‖^2)*X=X/‖eisEmbedding c‖^2 := by ring
  rw [hscale] at hp
  have harg (h : O) : (Real.sqrt X:ℂ)*(eisEmbedding h/eisEmbedding c)=a*eisEmbedding h := by
    dsimp [a]; ring
  simp_rw [harg] at hp
  rw [hp]
  exact h

end OAI.SevenEighths.Angular.PlaneVolume
