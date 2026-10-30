import AngularPhysicalAnnularFourierHeight
import AngularPhysicalPlainOutside
import OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.ReflectedAnnuli
open Set LocalLogFourier CenteredMomentSectorLocalization
open CenteredMomentReflectedAnnuli (annularProfile annularMass annularMass_nonneg annularMass_summable
  logWindow logWindowSchwartz logWindow_compact logWindow_smooth logWindow_support
  logWindow_derivative_bound logWindow_derivative_window)
open PlainDeletion (polynomial_plain)

def reflected (k:ℤ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) : ℝ→ℂ :=
  AnnularFourier.profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)

theorem reflected_smooth (k:ℤ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    ContDiffOn ℝ ∞ (reflected k W a b ha hs hW t) (Ioi 0) :=
  AnnularFourier.profile_contDiffOn k a b ha _

def logProfile (k:ℤ) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  positiveLogProfile logWindow (reflected k W a b ha hs hW t) s logWindow_compact logWindow_smooth
    (reflected_smooth k W a b ha hs hW t) hs0

@[simp] theorem logProfile_apply (k:ℤ) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t v : ℝ) :
    logProfile k W a b ha hs hW s hs0 t v =
      annularProfile (reflected k W a b ha hs hW t) s (Real.exp v) := rfl

theorem logProfile_tsupport (k:ℤ) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) :
    tsupport (logProfile k W a b ha hs hW s hs0 t) ⊆ Icc (-Real.log 4) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply logWindow_support
  intro hz
  exact hv (by change logWindow v*reflected k W a b ha hs hW t (s*Real.exp v)=0;rw [hz,zero_mul])

theorem normalized_annular_term (η : AngularCharacter) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0<s) (hY : 0<Y) :
    Dyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*Dyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp


end OAI.SevenEighths.Angular.ReflectedAnnuli

#print axioms OAI.SevenEighths.Angular.ReflectedAnnuli.normalized_annular_term
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectedAnnuli.normalized_annular_term
