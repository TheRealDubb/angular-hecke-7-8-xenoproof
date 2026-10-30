import AngularPhysicalPlainAbsolute
import AngularInverseRows
import AngularPhysicalProfileIdentity
import OAI.NumberTheory.DirichletL.Moments.HeckeTwist
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionary

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Angular.PlainRows
open OAI.SevenEighths.Angular.Dyadic
open InverseAmplification (polynomial_twistProfile)
open HeckeInverseAmplification (twistProfile)
open CenteredMomentTwist CompletedHeight CenteredMomentHeckeHeight CenteredMomentLattice
open CenteredMomentPrimeSlot (sqrt_inverse_cpow)
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : AngularCharacter) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, χ.idealHom I*W ((Ideal.absNorm I : ℝ)/X)

def twistedIdealSum (χ : AngularCharacter) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, χ.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem twistedIdealSum_scale (χ : AngularCharacter) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedIdealSum χ W t X = (X : ℂ) ^ (Complex.I * t) *
      idealSum χ (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedIdealSum idealSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

def rowTwistedSum (η : AngularCharacter) (m A₀ z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (η.idealHom I*CanonicalRowCompletion.idealRowHom (m^6*(A₀*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem rowTwistedSum_eq (η χ : AngularCharacter) (m A₀ z : O)
    (hrow : ∀ n, χ.elementCoeff n=CanonicalRowCompletion.rowTwist
      η.elementHom.toMonoidHom m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := InverseRows.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

lemma plain_zero_height (χ : AngularCharacter) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>χ.idealHom I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : Dyadic.NonzeroIdeal,χ.idealHom I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,χ.idealHom I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,Dyadic.norm,Dyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    Dyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_height_norm (χ:AngularCharacter)(W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(t X:ℝ)(hX:0<X):
    ‖(Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X‖=
      ‖polynomial χ false W X 0 t‖:=by
  have hp:(normPowerProfile W a b ha hs hW t:ℝ→ℂ)=twistProfile W 0 t:=by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm (Complex.I) (t:ℂ)]
    ring
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hi:idealSum χ (normPowerProfile W a b ha hs hW t) X=
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X:=by
    simp [idealSum,twistedIdealSum]
  rw [hi]
  have he:(Real.sqrt X:ℂ)⁻¹*((X:ℂ)^(Complex.I*t)*
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X)=
      (X:ℂ)^(Complex.I*t)*polynomial χ false W X 0 t:=by
    rw [←polynomial_twistProfile,←hp,plain_zero_height _ _ X hX]
    ring
  rw [he,norm_mul,norm_real_imaginary_power X t hX,one_mul]

#print axioms rowTwistedSum_eq
#print axioms plain_height_norm
end SevenEighths.Angular.PlainRows
end
end OAI
