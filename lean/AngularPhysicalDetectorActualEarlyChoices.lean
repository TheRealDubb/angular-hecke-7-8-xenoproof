import AngularPhysicalDetectorActualHeightChoices

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

/-- Fix rho and the common counting mesh first, then the physical lengths
and their minimum rmin. This chooses e before the excluded set S, its ray
modulus, and the degree J. The late height choice is a separate theorem.
No analytic bound or finite-family transfer is assumed here. -/
theorem actual_early_parameter_choices (rho epsm R rmin mesh : ℝ)
    (hrho : 0<rho) (hem : 0<epsm) (hR : 0<R) (hr : 0<rmin) (hm : 0<mesh) :
    ∃epsw e phaseE phaseK sourceK sourceCost : ℝ,
      0<epsw ∧ epsw≤1/1000 ∧ epsw≤epsm/300 ∧ epsw≤rho ∧
      0<e ∧ e<1/1000 ∧ e≤rho ∧
      0<phaseE ∧ 0<phaseK ∧ 8*e*R+phaseK≤phaseE ∧ phaseE<rmin*mesh ∧
      0<sourceK ∧ sourceK≤1 ∧ 0<sourceCost ∧
      12*e*((22:ℝ)+2)+8*sourceK+2*sourceCost≤epsw/2 := by
  let epsw : ℝ := min (1/2000) (min (epsm/600) (rho/2))
  have hew : 0<epsw := by dsimp [epsw];positivity
  have hew1 : epsw≤1/2000 := min_le_left _ _
  have hewm : epsw≤epsm/600 := (min_le_right _ _).trans (min_le_left _ _)
  have hewr : epsw≤rho/2 := (min_le_right _ _).trans (min_le_right _ _)
  let e : ℝ := min (rho/2) (min (1/2000) (min (epsw/2304) (rmin*mesh/(64*(R+1)))))
  have he : 0<e := by dsimp [e];positivity
  have her : e≤rho/2 := min_le_left _ _
  have he1 : e≤1/2000 := (min_le_right _ _).trans (min_le_left _ _)
  have hes : e≤epsw/2304 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hep : e≤rmin*mesh/(64*(R+1)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hep' : e*(64*(R+1))≤rmin*mesh :=
    (le_div_iff₀ (by positivity : 0<64*(R+1))).mp hep
  refine ⟨epsw,e,rmin*mesh/2,rmin*mesh/8,epsw/64,epsw/16,
    hew,by linarith,by linarith,by linarith,he,by linarith,by linarith,
    by positivity,by positivity,?_,?_,by positivity,?_,by positivity,?_⟩
  · nlinarith [mul_pos hr hm]
  · nlinarith [mul_pos hr hm]
  · linarith
  · nlinarith

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_early_parameter_choices
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_early_parameter_choices
