import AngularPhysicalReciprocalGlobal
import AngularPhysicalDetectorScale

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalSignalBounds

/-- Polynomial reciprocal growth for actual nonprincipal targets. The
constant precedes the character; the finite conductor remains explicit. -/
theorem nonprincipal_polynomial_reciprocal_bound (angularCap : ℕ) (a : ℝ)
    (ha : PhysicalZeroSupremum.beta angularCap<a) :
    ∃C : ℝ,0<C ∧ ∀χ : AngularCharacter,χ.k.natAbs≤angularCap →
      (χ.k≠0 ∨ χ.residue≠1) → ∀s : ℂ,a≤s.re →
      ‖PhysicalReciprocal.reciprocal χ s‖≤C*(χ.modulus.absNorm:ℝ)^2*(1+|s.im|^2) := by
  let e : ℝ := min ((a-PhysicalZeroSupremum.beta angularCap)/16) (1/2000)
  have he : 0<e := by dsimp [e];positivity
  have he1 : e<1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have heb : PhysicalZeroSupremum.beta angularCap+8*e≤a := by
    have h := min_le_left ((a-PhysicalZeroSupremum.beta angularCap)/16) (1/2000)
    change e≤(a-PhysicalZeroSupremum.beta angularCap)/16 at h
    linarith
  obtain ⟨D,hD,hbound⟩ := PhysicalReciprocal.nonprincipal_reciprocal_subpower
    angularCap e 1 he he1 (by norm_num)
  refine ⟨36*D,by positivity,?_⟩
  intro χ horder hnp s hs
  have hb := hbound χ horder hnp s (heb.trans hs)
  rw [Real.rpow_one] at hb
  have hc := PhysicalDetectorDyadic.presentationComplexity_le_of_modulus_le
    χ (χ.modulus.absNorm:ℝ) s.im le_rfl
  have hp : (3+|s.im|)^2≤18*(1+|s.im|^2) := by
    nlinarith [sq_nonneg (|s.im|-3),sq_nonneg |s.im|]
  calc
    _ ≤ D*(2*(χ.modulus.absNorm:ℝ)^2*(3+|s.im|)^2) :=
      hb.trans (mul_le_mul_of_nonneg_left hc hD.le)
    _ ≤ D*(2*(χ.modulus.absNorm:ℝ)^2*(18*(1+|s.im|^2))) := by gcongr
    _ = _ := by ring

end OAI.SevenEighths.Angular.PhysicalSignalBounds

#print axioms OAI.SevenEighths.Angular.PhysicalSignalBounds.nonprincipal_polynomial_reciprocal_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalSignalBounds.nonprincipal_polynomial_reciprocal_bound
