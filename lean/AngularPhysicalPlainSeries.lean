import AngularPhysicalPolynomial
import AngularPhysicalNonprincipalStrip

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace OAI.SevenEighths.Angular.PlainDyadic
open OAI.SevenEighths.Angular.Dyadic FamilyContinuation

abbrev series (χ : AngularCharacter) (s : ℂ) : ℂ := LFunction χ s

theorem nonprincipal_entire (χ : AngularCharacter) (hχ : χ.k ≠ 0 ∨ χ.residue ≠ 1) :
    Differentiable ℂ (series χ) := by
  by_cases hk : χ.k = 0
  · exact TypeZeroEntire.LFunction_entire χ hk (hχ.resolve_left (not_not.mpr hk))
  · exact FamilyContinuation.LFunction_differentiable χ hk

theorem series_eq_tsum (χ : AngularCharacter) {s : ℂ} (hs : 1 < s.re) :
    series χ s =
      ∑' I : NonzeroIdeal, coefficient χ false I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ false I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ false I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ false I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ false 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ false I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ false I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
    simp only [Dyadic.norm, Complex.ofReal_natCast]
  rw [hc]
  exact FamilyContinuation.LFunction_eq_series χ s hs

#print axioms nonprincipal_entire
#print axioms series_eq_tsum
end OAI.SevenEighths.Angular.PlainDyadic
