import AngularPhysicalAnalyticEntireness
import AngularRightSeriesBounds
import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
import OAI.NumberTheory.DirichletL.LogarithmicControl

/-! A regular analytic input for the actual angular family. Only the genuine
type-zero principal pole is removed. Nonprincipal L-functions are not
multiplied by s-1, so no artificial zero at one enters the zero supremum. -/
noncomputable section
open scoped Classical Topology
open Set Complex
namespace OAI.SevenEighths.Angular.PhysicalLogarithmicInput
open FiniteIdentification

def regular (χ : AngularCharacter) (s : ℂ) : ℂ :=
  if hk : χ.k = 0 then HeckeLogarithmicInput.regular (toFinite χ hk) s
  else FamilyContinuation.LFunction χ s

theorem regular_eq_typeZero (χ : AngularCharacter) (hk : χ.k = 0) :
    regular χ = HeckeLogarithmicInput.regular (toFinite χ hk) := by
  funext s
  simp [regular,hk]

theorem regular_eq_nonprincipal (χ : AngularCharacter)
    (hχ : χ.k ≠ 0 ∨ χ.residue ≠ 1) : regular χ = FamilyContinuation.LFunction χ := by
  by_cases hk : χ.k = 0
  · have hr := hχ.resolve_left (not_not.mpr hk)
    rw [regular_eq_typeZero χ hk,
      HeckeLogarithmicInput.regular_eq_nonprincipal (toFinite χ hk) hr]
    funext s
    exact (TypeZeroEntire.LFunction_eq_finite χ hk hr s).symm
  · funext s
    simp [regular,hk]

theorem regular_differentiableAt (χ : AngularCharacter) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regular χ) s := by
  by_cases hk : χ.k = 0
  · rw [regular_eq_typeZero χ hk]
    exact HeckeLogarithmicInput.regular_differentiableAt (toFinite χ hk) hs
  · rw [regular_eq_nonprincipal χ (Or.inl hk)]
    exact FamilyContinuation.LFunction_differentiable χ hk s

theorem regular_eq_principal_factor (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue = 1) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    regular χ s = ((s-1)*FamilyContinuation.LFunction χ s)/(s+1) := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [regular_eq_typeZero χ hk]
  simp only [HeckeLogarithmicInput.regular,
    show (toFinite χ hk).residue = 1 from hχ, ite_true,
    HeckePrincipalStrip.sourceNormalized, HeckeOrigin.poleRemoved_eq _ h0 h1]
  rw [typeZero_LFunction χ hk s h0 h1]

theorem regular_principal_one_ne_zero (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue = 1) : regular χ 1 ≠ 0 := by
  rw [regular_eq_typeZero χ hk]
  simp only [HeckeLogarithmicInput.regular,
    show (toFinite χ hk).residue = 1 from hχ, ite_true,
    HeckePrincipalStrip.sourceNormalized]
  exact div_ne_zero (HeckeOrigin.poleRemoved_one_ne_zero (toFinite χ hk) hχ)
    (by norm_num)

theorem regular_norm_le (χ : AngularCharacter) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖regular χ s‖ ≤ HeckeReciprocalBound.bound σ := by
  by_cases hk : χ.k = 0
  · rw [regular_eq_typeZero χ hk]
    exact HeckeLogarithmicInput.regular_norm_le (toFinite χ hk) hσ hs
  · rw [regular_eq_nonprincipal χ (Or.inl hk)]
    exact PlainReflection.LFunction_norm_le χ hσ hs

theorem regular_inverse_norm_le (χ : AngularCharacter) {s : ℂ}
    (hs : (3/2:ℝ) ≤ s.re) :
    ‖(regular χ s)⁻¹‖ ≤ 5*HeckeReciprocalBound.bound (3/2) := by
  by_cases hk : χ.k = 0
  · rw [regular_eq_typeZero χ hk]
    exact HeckeLogarithmicInput.regular_inverse_norm_le (toFinite χ hk) hs
  · rw [regular_eq_nonprincipal χ (Or.inl hk)]
    have h := PlainReflection.inverse_LFunction_norm_le χ (by norm_num : (1:ℝ)<3/2) hs
    have hB : 0 ≤ HeckeReciprocalBound.bound (3/2) := tsum_nonneg (fun _ => norm_nonneg _)
    linarith

theorem regular_disk_differentiable (χ : AngularCharacter) {a e t : ℝ}
    (ha : (1/2:ℝ) ≤ a) (he : 0 < e) :
    DifferentiableOn ℂ (regular χ) (Metric.ball ((2:ℂ)+t*I) (2-a-2*e)) := by
  intro z hz
  exact (regular_differentiableAt χ (by
    have hr := LogarithmicControl.disk_re_gt hz
    linarith)).differentiableWithinAt

end OAI.SevenEighths.Angular.PhysicalLogarithmicInput

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_eq_typeZero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_eq_typeZero

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_eq_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_eq_nonprincipal

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_differentiableAt
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_differentiableAt

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_eq_principal_factor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_eq_principal_factor

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_principal_one_ne_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_principal_one_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_norm_le

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_inverse_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_inverse_norm_le

#print axioms OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_disk_differentiable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLogarithmicInput.regular_disk_differentiable
