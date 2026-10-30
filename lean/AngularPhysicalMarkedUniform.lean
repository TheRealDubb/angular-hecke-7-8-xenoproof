import AngularPhysicalFourierEnergy
import AngularPhysicalProfileIdentity
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace SevenEighths.Angular.MarkedUniform
open OAI.SevenEighths.Angular.Dyadic InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open RawFourier InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge

private theorem clipped_one_zero (W : ℝ→ℂ) : clippedTest W 1 0=W := by
  funext x
  simp [clippedTest,childLogTest,logPhase]

theorem family_mode_integrable (χ : AngularCharacter) (A : ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t D : ℝ) (hD : 0<D) :
    Integrable (fun v : ℝ=>familyDensity scaled reverse n U tstar r σ t 1 v*
      (polynomial χ true (childLogTest referenceWindow v) D 0 0*A)) := by
  simpa only [familyDensity,zero_add,mul_assoc] using
    (polynomial_mode_integrable χ true (logSource scaled reverse n U tstar r σ t)
      referenceWindow (13/4) 1 0 D hD
      (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)).mul_const A

theorem family_polynomial_fourier (χ : AngularCharacter) (A : ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t D : ℝ) (hD : 0<D) :
    polynomial χ true (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A=
      ∫v : ℝ,familyDensity scaled reverse n U tstar r σ t 1 v*
        (polynomial χ true (childLogTest referenceWindow v) D 0 0*A) := by
  have h:=polynomial_clipped_fourier χ true
    (inverseSourceSchwartz scaled reverse n U tstar r σ t) (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow (13/4) 1 0 D (by norm_num) hD
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy)
  rw [clipped_one_zero] at h
  rw [h,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards with v
  simp only [familyDensity,logSource_eq_logSchwartz,zero_add,mul_assoc]

theorem moving_finite_energy (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type*}(rows : Finset ι)
      (χ : ι→AngularCharacter)(A : ι→ℂ)(D E : ℝ),0<D→0≤E→
    (∀v : ℝ,(∑u∈rows,‖polynomial (χ u) true (childLogTest referenceWindow v) D 0 0*A u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀scaled reverse : Bool,∀n : ℕ,n≤2→∀U : ℝ,0<U→
    ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈rows,‖polynomial (χ u) true
      (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A u‖^2)
      ≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro ι rows χ A D E hD hE href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  have hb:=polynomial_clipped_energy rows χ true A W (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t) (W.smooth ⊤)
    referenceWindow (13/4) 1 0 D E J (by norm_num) hD hE
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy) href
  rw [clipped_one_zero] at hb
  simp only [norm_zero,add_zero,one_pow,mul_one] at hb
  have hm:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  apply hb.trans
  calc
    _≤E*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hE
    _= _:=by rw [mul_pow,←pow_mul];ring_nf

#print axioms family_polynomial_fourier
#print axioms moving_finite_energy
end SevenEighths.Angular.MarkedUniform
end
end OAI
