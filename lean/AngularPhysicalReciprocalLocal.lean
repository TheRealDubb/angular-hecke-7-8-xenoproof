import AngularPhysicalLogarithmicDisk
import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

/-! Actual analytic reciprocal with the principal-pole convention.
Only local identities and right-half-plane differentiability are selected. -/
noncomputable section
open scoped Classical Topology
open Complex
namespace OAI.SevenEighths.Angular.PhysicalReciprocal
open PhysicalLogarithmicInput

def reciprocal (χ : AngularCharacter) (s : ℂ) : ℂ :=
  if χ.k = 0 ∧ χ.residue = 1 then
    ((s-1)/(s+1))*(regular χ s)⁻¹ else (regular χ s)⁻¹

theorem reciprocal_eq_nonprincipal (χ : AngularCharacter)
    (hχ : χ.k ≠ 0 ∨ χ.residue ≠ 1) (s : ℂ) :
    reciprocal χ s = (FamilyContinuation.LFunction χ s)⁻¹ := by
  have hp : ¬(χ.k = 0 ∧ χ.residue = 1) := by tauto
  simp only [reciprocal,ite_eq_right hp,regular_eq_nonprincipal χ hχ]

theorem reciprocal_principal_one (χ : AngularCharacter)
    (hk : χ.k = 0) (hχ : χ.residue = 1) : reciprocal χ 1 = 0 := by
  have hp : χ.k = 0 ∧ χ.residue = 1 := ⟨hk,hχ⟩
  simp only [reciprocal,ite_eq_left hp,sub_self,zero_div,zero_mul]

theorem reciprocal_eq_inv (χ : AngularCharacter) (s : ℂ) (hs : 0 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1) :
    reciprocal χ s = (FamilyContinuation.LFunction χ s)⁻¹ := by
  by_cases hp : χ.k = 0 ∧ χ.residue = 1
  · have h1 := hpole hp.1 hp.2
    have hplus : s+1 ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
      linarith
    simp only [reciprocal,ite_eq_left hp,
      regular_eq_principal_factor χ hp.1 hp.2 hs h1]
    by_cases hL : FamilyContinuation.LFunction χ s = 0
    · simp [hL]
    · field_simp [hplus,sub_ne_zero.mpr h1,hL] <;> ring
  · exact reciprocal_eq_nonprincipal χ (by tauto) s

theorem reciprocal_eq_inverseSeries (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    reciprocal χ s = IdealEuler.inverseSeries χ.idealHom s := by
  rw [reciprocal_eq_inv χ s (by linarith)
    (fun _ _ he => by norm_num [he] at hs),
    FamilyContinuation.LFunction_eq_series χ s hs,AngularCharacter.series]
  exact (IdealEuler.inverseSeries_eq_inv χ.idealHom χ.norm_idealHom_le_one s hs).symm

theorem reciprocal_norm_le_regular_inverse (χ : AngularCharacter) {s : ℂ}
    (hs : 0 ≤ s.re) : ‖reciprocal χ s‖ ≤ ‖(regular χ s)⁻¹‖ := by
  by_cases hp : χ.k = 0 ∧ χ.residue = 1
  · simp only [reciprocal,ite_eq_left hp,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (LogarithmicControl.principal_regularizer_norm_le_one hs)
  · simp only [reciprocal,ite_eq_right hp,le_refl]

theorem reciprocal_norm_le (χ : AngularCharacter) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖reciprocal χ s‖ ≤ HeckeReciprocalBound.bound σ := by
  rw [reciprocal_eq_inv χ s (by linarith) (fun _ _ he => by norm_num [he] at hs; linarith)]
  exact PlainReflection.inverse_LFunction_norm_le χ hσ hs

theorem reciprocal_differentiableAt_right (χ : AngularCharacter) {s : ℂ}
    (hs : 1 < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have hf := (FamilyContinuation.LFunction_differentiableAt χ s
    (by linarith) (by intro h; norm_num [h] at hs)).inv
    (FamilyContinuation.LFunction_ne_zero χ s hs)
  have he : reciprocal χ =ᶠ[nhds s]
      (fun z => (FamilyContinuation.LFunction χ z)⁻¹) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds hs] with z hz
    exact reciprocal_eq_inv χ z (by linarith) (fun _ _ h => by norm_num [h] at hz)
  exact hf.congr_of_eventuallyEq he

def presentationComplexity (χ : AngularCharacter) (t : ℝ) : ℝ :=
  ((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)*PhysicalLogarithmic.complexity χ t

end OAI.SevenEighths.Angular.PhysicalReciprocal

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_eq_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_eq_nonprincipal

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_principal_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_principal_one

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_eq_inv
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_eq_inv

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_eq_inverseSeries
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_eq_inverseSeries

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_norm_le_regular_inverse
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_norm_le_regular_inverse

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_norm_le

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_differentiableAt_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.reciprocal_differentiableAt_right
