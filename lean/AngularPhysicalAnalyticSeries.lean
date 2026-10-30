import AngularPhysicalPolynomial
import AngularPhysicalReciprocalLocal
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace OAI.SevenEighths.Angular.Dyadic
open FamilyContinuation
def series (χ : AngularCharacter) (inverse : Bool) (s : ℂ) : ℂ :=
  if inverse then PhysicalReciprocal.reciprocal χ s else LFunction χ s

theorem series_eq_tsum (χ : AngularCharacter) (inverse : Bool) {s : ℂ} (hs : 1 < s.re) :
    series χ inverse s =
      ∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ inverse I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ inverse 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
    simp only [norm, Complex.ofReal_natCast]
  rw [hc]
  cases inverse
  · exact FamilyContinuation.LFunction_eq_series χ s hs
  · change PhysicalReciprocal.reciprocal χ s = _
    rw [PhysicalReciprocal.reciprocal_eq_inverseSeries χ s hs]
    apply tsum_congr
    intro I
    simp only [coefficient,  ite_true, IdealEuler.weighted,
      IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring


end OAI.SevenEighths.Angular.Dyadic

#print axioms OAI.SevenEighths.Angular.Dyadic.series_eq_tsum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.Dyadic.series_eq_tsum
