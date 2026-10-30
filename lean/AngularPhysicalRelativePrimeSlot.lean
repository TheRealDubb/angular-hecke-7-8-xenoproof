import AngularPhysicalRelativeFiniteProduct
import AngularPhysicalPlainExpansion
import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.RelativePrime
open PlainRows CanonicalRowCompletion
open HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentPrimeSlot (primePool sqrt_inverse_cpow)
open CenteredMomentPrimeSlotShift (norm_height_split)
local notation "O" => ActualEisensteinCubic.O

def normalizedSlot (η:AngularCharacter) (m A z:O) (S:Finset (Ideal O))
    (β:Ideal O→ℂ) (t P:ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

/-- Exact finite prime polynomial, including the common height phase and all
natural support holes. The opposite-type slot premise is essential. -/
theorem relative_normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ ν:AngularCharacter) (hk:χ.k+ν.k=0) (m A z:O)
    (hrow:∀n:O,χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun I=>ν.idealHom I*annularWeight W D σ v I) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H (finiteProduct χ ν hk) W b D σ (t+v) := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I:=(Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero)
  have hc:=InverseRows.idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t v hN hD
  simp only [Complex.ofReal_natCast] at hn
  change (D:ℂ)^(-(1/2:ℂ))*
    ((ν.idealHom I*(W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)))*χ.idealHom I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*(χ.idealHom I*ν.idealHom I))*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [←finiteProduct_idealCoeff χ ν hk I,hn]; unfold annularWeight; ring

theorem relative_normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ ν:AngularCharacter) (hk:χ.k+ν.k=0) (m A z:O)
    (hrow:∀n:O,χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D)
      (fun I=>ν.idealHom I*annularWeight W D σ v I) t D‖^2=
      ‖rayPrimePolynomial M H (finiteProduct χ ν hk) W b D σ (t+v)‖^2 := by
  rw [relative_normalizedSlot_eq_ray M H η χ ν hk m A z hrow W b D σ t v hD,
    norm_mul,CenteredMomentTwist.norm_real_imaginary_power D t hD,one_mul]

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.relative_normalizedSlot_eq_ray
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.relative_normalizedSlot_eq_ray

#print axioms OAI.SevenEighths.Angular.RelativePrime.relative_normalizedSlot_norm_sq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.relative_normalizedSlot_norm_sq
