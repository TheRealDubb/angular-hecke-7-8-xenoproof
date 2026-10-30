import AngularPhysicalFinalAssembly

/- Narrow semantic check of the public statement and the physical series.
This is an author-side check against the retained caches, not an independent
kernel replay of the full imported project. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalPublicStatementCheck

example : ∀(χ : AngularCharacter)(s : ℂ),
    (7/8:ℝ)<s.re → (χ.k=0 → χ.residue=1 → s≠1) →
    FamilyContinuation.LFunction χ s≠0 :=
  PhysicalFinalAssembly.LFunction_ne_zero_of_seven_eighths_lt_re

theorem actual_series_identification (χ : AngularCharacter) (s : ℂ) (hs : 1<s.re) :
    FamilyContinuation.LFunction χ s=
      ∑'I : Ideal ActualEisensteinCubic.O,χ.idealHom I/(Ideal.absNorm I:ℂ)^s := by
  rw [FamilyContinuation.LFunction_eq_series χ s hs,χ.series_eq_tsum]
  rfl

end OAI.SevenEighths.Angular.PhysicalPublicStatementCheck
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.LFunction_ne_zero_of_seven_eighths_lt_re
#print axioms OAI.SevenEighths.Angular.PhysicalPublicStatementCheck.actual_series_identification
#print axioms OAI.SevenEighths.Angular.AngularCharacter.idealHom_span
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalFinalAssembly.LFunction_ne_zero_of_seven_eighths_lt_re
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AngularCharacter.idealHom_span
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AngularCharacter.elementCoeff_eq
