import AngularPhysicalReciprocalLocal

/- Pointwise analytic reciprocal under an explicit nonvanishing premise.
No zero supremum, seed bound, or proposed zero-free conclusion is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalReciprocal
open PhysicalLogarithmicInput

theorem reciprocal_differentiableAt_of_regular_ne_zero (χ : AngularCharacter)
    {s : ℂ} (hs : 0<s.re) (hne : regular χ s≠0) :
    DifferentiableAt ℂ (reciprocal χ) s := by
  have hi := (regular_differentiableAt χ hs).inv hne
  by_cases hp : χ.k=0 ∧ χ.residue=1
  · have hplus : s+1≠0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
      linarith
    have heq : reciprocal χ=(fun z : ℂ=>((z-1)/(z+1))*(regular χ z)⁻¹) := by
      funext z
      simp only [reciprocal,ite_eq_left hp]
    rw [heq]
    have hid : DifferentiableAt ℂ (fun z : ℂ=>z) s := differentiableAt_id
    exact ((hid.sub_const (1:ℂ)).div (hid.add_const (1:ℂ)) hplus).mul hi
  · have heq : reciprocal χ=(fun z : ℂ=>(regular χ z)⁻¹) := by
      funext z
      simp only [reciprocal,ite_eq_right hp]
    rw [heq]
    exact hi

theorem reciprocal_differentiableAt_of_nonprincipal_ne_zero (χ : AngularCharacter)
    (hχ : χ.k≠0 ∨ χ.residue≠1) {s : ℂ} (hs : 0<s.re)
    (hne : FamilyContinuation.LFunction χ s≠0) :
    DifferentiableAt ℂ (reciprocal χ) s := by
  apply reciprocal_differentiableAt_of_regular_ne_zero χ hs
  simpa only [regular_eq_nonprincipal χ hχ] using hne

theorem reciprocal_differentiableAt_principal_one (χ : AngularCharacter)
    (hk : χ.k=0) (hχ : χ.residue=1) :
    DifferentiableAt ℂ (reciprocal χ) 1 :=
  reciprocal_differentiableAt_of_regular_ne_zero χ (by norm_num)
    (regular_principal_one_ne_zero χ hk hχ)

end OAI.SevenEighths.Angular.PhysicalReciprocal
#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_differentiableAt_of_regular_ne_zero
#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_differentiableAt_of_nonprincipal_ne_zero
#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_differentiableAt_principal_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_differentiableAt_of_regular_ne_zero
