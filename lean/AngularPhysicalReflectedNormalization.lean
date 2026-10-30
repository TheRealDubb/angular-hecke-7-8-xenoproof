import AngularPhysicalNormalizedOneEnergy
import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace OAI.SevenEighths.Angular.NormalizedReflectionEnergy
open AnnularFourier
open AnnularEnergy (plain_annular_separation plain_density_integrable)
open CenteredMomentReflectedProfileMeasure (logWindow row_density_energy)
open CenteredMomentReflectedUniformPair (heightScale normalized_density_bound envelope
  envelope_pos envelope_integrable envelope_integral)

open CenteredMomentSectorLocalization
open CenteredMomentReflectedNormalization (actual_log_window)

lemma polynomial_const (χ : AngularCharacter) (W : ℝ→ℂ) (X : ℝ) (c : ℂ) :
    Dyadic.polynomial χ false (fun x=>c*W x) X 0 0=
      c*Dyadic.polynomial χ false W X 0 0 := by
  unfold Dyadic.polynomial
  have he (I : Dyadic.NonzeroIdeal) :
      Dyadic.summand χ false (fun x=>c*W x) X 0 0 I=
        c*Dyadic.summand χ false W X 0 0 I := by
    unfold Dyadic.summand
    ring
  simp_rw [he,tsum_mul_left]
  ring

lemma normalized_profile_actual (ℓ:ℤ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (B n:ℕ) (s t x : ℝ) :
    normalizedReflected ℓ CenteredMomentReflectedAnnuli.logWindow W a b ha hs hW B n s t x=
      (heightScale B n s t:ℂ)*CenteredMomentReflectedAnnuli.annularProfile
        (profile ℓ a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) s x := by
  unfold normalizedReflected
  rw [actual_log_window]
  unfold CenteredMomentReflectedAnnuli.annularProfile
  ring

theorem actual_annular_normalization (χ:AngularCharacter) (ℓ:ℤ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (B n:ℕ)
    (k : ℤ) (t Y : ℝ) :
    (Real.sqrt (dyadicScale k):ℂ)*Dyadic.polynomial χ false
      (CenteredMomentReflectedAnnuli.annularProfile
        (profile ℓ a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) (dyadicScale k))
      (dyadicScale k*Y) 0 0=
      (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
        Dyadic.polynomial χ false
          (normalizedReflected ℓ CenteredMomentReflectedAnnuli.logWindow W a b ha hs hW B n (dyadicScale k) t)
          (dyadicScale k*Y) 0 0 := by
  have hf : normalizedReflected ℓ CenteredMomentReflectedAnnuli.logWindow W a b ha hs hW B n (dyadicScale k) t=
      (fun x=>(heightScale B n (dyadicScale k) t:ℂ)*
        CenteredMomentReflectedAnnuli.annularProfile
          (profile ℓ a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) (dyadicScale k) x) :=
    funext (normalized_profile_actual ℓ W a b ha hs hW B n (dyadicScale k) t)
  rw [hf,polynomial_const]
  have hh : (1+‖t‖)^n*CenteredMomentReflectedAnnuli.annularMass B k*
      heightScale B n (dyadicScale k) t=Real.sqrt (dyadicScale k) := by
    unfold CenteredMomentReflectedAnnuli.annularMass heightScale
    have ht : (1+‖t‖)^n≠0 := ne_of_gt (by positivity)
    have hs : (1+dyadicScale k)^B≠0 := ne_of_gt (by have := dyadicScale_pos k;positivity)
    field_simp
  have hc : (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
      (heightScale B n (dyadicScale k) t:ℂ)=(Real.sqrt (dyadicScale k):ℂ) := by
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,hh]
  rw [←mul_assoc _ (heightScale B n (dyadicScale k) t:ℂ),hc]


end OAI.SevenEighths.Angular.NormalizedReflectionEnergy

#print axioms OAI.SevenEighths.Angular.NormalizedReflectionEnergy.actual_annular_normalization
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NormalizedReflectionEnergy.actual_annular_normalization
