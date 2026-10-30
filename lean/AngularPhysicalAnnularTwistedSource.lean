import AngularPhysicalOriginalConjugateReflection
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.NaturalReflection
open CenteredMomentNaturalPrimitive AnnularFourier
open CenteredMomentReflectionDeletion (SmoothIdeal norm)

lemma polynomial_twisted_source (χ:AngularCharacter) (W:ℝ→ℂ) (X t:ℝ) (hX:0<X) :
    Dyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      Dyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold Dyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm:=HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (Dyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold Dyadic.summand Dyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,Dyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [Dyadic.norm,HeckeDyadic.shift,Dyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

theorem uniformTwistedSchwartz_support (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (t:ℝ) :
    Function.support (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t:ℝ→ℂ)⊆Set.Icc a b := by
  intro x hx
  apply hs
  intro hz
  apply hx
  rw [CompletedHeight.uniformTwistedSchwartz_apply,CompletedHeight.normTwistedSource,hz,mul_zero]

end OAI.SevenEighths.Angular.NaturalReflection

#print axioms OAI.SevenEighths.Angular.NaturalReflection.polynomial_twisted_source
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReflection.polynomial_twisted_source
