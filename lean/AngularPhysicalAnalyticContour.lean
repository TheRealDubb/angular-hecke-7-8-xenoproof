import AngularPhysicalAnalyticMellin

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.Angular.Dyadic
open FamilyContinuation

def integrand (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    series χ inverse (s+shift σ freq)

theorem series_norm_le (χ : AngularCharacter) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact PlainReflection.LFunction_norm_le χ hb hs
  · exact PhysicalReciprocal.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : AngularCharacter) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact FamilyContinuation.LFunction_differentiableAt χ s
      (by linarith) (by intro h; norm_num [h] at hs)
  · exact PhysicalReciprocal.reciprocal_differentiableAt_right χ hs

theorem series_differentiableAt_nonprincipal (χ : AngularCharacter) (hχ : χ.k ≠ 0 ∨ χ.residue ≠ 1)
    (inverse : Bool) {s : ℂ} (hz : inverse=true → LFunction χ s≠0) :
    DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact PhysicalAnalytic.nonprincipal_entire χ hχ s
  · have he : series χ true = fun z => (LFunction χ z)⁻¹ := by
      funext z
      change PhysicalReciprocal.reciprocal χ z = _
      exact PhysicalReciprocal.reciprocal_eq_nonprincipal χ hχ z
    rw [he]
    exact (PhysicalAnalytic.nonprincipal_entire χ hχ s).inv (hz rfl)

theorem integrand_differentiableAt (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    DifferentiableAt ℂ (integrand χ inverse W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem integrand_norm (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ inverse (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*HeckeReciprocalBound.bound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ inverse W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ inverse hc (by simp))
  positivity

theorem finite_rectangle (χ : AngularCharacter) (hχ : χ.k ≠ 0 ∨ χ.residue ≠ 1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ inverse W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ inverse (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ inverse W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : AngularCharacter) (hχ : χ.k ≠ 0 ∨ χ.residue ≠ 1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ inverse W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.Angular.Dyadic

end

end OAI

#print axioms OAI.SevenEighths.Angular.Dyadic.series_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.series_norm_le

#print axioms OAI.SevenEighths.Angular.Dyadic.series_differentiableAt_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.series_differentiableAt_right

#print axioms OAI.SevenEighths.Angular.Dyadic.series_differentiableAt_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.series_differentiableAt_nonprincipal

#print axioms OAI.SevenEighths.Angular.Dyadic.integrand_differentiableAt
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.integrand_differentiableAt

#print axioms OAI.SevenEighths.Angular.Dyadic.integrand_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.integrand_norm

#print axioms OAI.SevenEighths.Angular.Dyadic.integrand_vertical_integrable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.integrand_vertical_integrable

#print axioms OAI.SevenEighths.Angular.Dyadic.finite_rectangle
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.finite_rectangle

#print axioms OAI.SevenEighths.Angular.Dyadic.polynomial_finite_shift
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.polynomial_finite_shift
