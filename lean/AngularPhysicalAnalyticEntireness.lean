import AngularTypeZeroEntire
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalAnalytic
theorem nonprincipal_entire (χ : AngularCharacter)
    (hnonprincipal : χ.k ≠ 0 ∨ χ.residue ≠ 1) :
    Differentiable ℂ (FamilyContinuation.LFunction χ) := by
  by_cases hk : χ.k = 0
  · exact TypeZeroEntire.LFunction_entire χ hk (hnonprincipal.resolve_left (not_not.mpr hk))
  · exact FamilyContinuation.LFunction_differentiable χ hk


end OAI.SevenEighths.Angular.PhysicalAnalytic

#print axioms OAI.SevenEighths.Angular.PhysicalAnalytic.nonprincipal_entire
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalAnalytic.nonprincipal_entire
