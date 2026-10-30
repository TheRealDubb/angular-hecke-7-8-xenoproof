import AngularPhysicalDetectorActualRealBudget
import AngularPhysicalDetectorActualEarlyChoices
import AngularPhysicalDetectorSlotSupply
import AngularPhysicalDetectorMesh

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

/-- Numerical and slot data for the retained band, with dmin=1/200 and
dmax=5/6. The excluded set, ray modulus, target, and profile degree are not
inputs. Their analytic hypotheses still require separate suppliers. -/
structure ActualRetainedParameters where
  N : ℕ
  I : ℕ
  ell : Fin N → ℝ
  rho : ℝ
  epsm : ℝ
  R : ℝ
  mesh : ℝ
  nu : ℝ
  countCost : ℝ
  ζ : ℝ
  μ : ℝ
  pad : ℝ
  normalizerLoss : ℝ
  dyadLoss : ℝ
  saving : ℝ
  loss : ℝ
  phaseCost : ℝ
  rmin : ℝ
  epsw : ℝ
  e : ℝ
  eps : ℝ
  phaseE : ℝ
  phaseK : ℝ
  sourceK : ℝ
  sourceCost : ℝ
  rho_pos : 0 < rho
  rho_small : rho ≤ 1/100000000
  mesh_conditions : 0 < epsm ∧ epsm ≤ 1 ∧ 0 < R ∧ 0 < mesh ∧ 0 < nu ∧
    0 < countCost ∧ R ≤ PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2)
  slot_conditions : 0 < N ∧ Even N ∧ 0 < rmin ∧ Function.Injective ell ∧
    (∑j,ell j) = 1/6 ∧ ∀j,0 < ell j ∧ (5/6)*rmin ≤ ell j ∧ ell j ≤ (1/200)*R
  early_conditions : 0 < epsw ∧ epsw ≤ 1/1000 ∧ epsw ≤ epsm/300 ∧ epsw ≤ rho ∧
    0 < e ∧ e < 1/1000 ∧ e ≤ rho ∧
    0 < phaseE ∧ 0 < phaseK ∧ 8*e*R+phaseK ≤ phaseE ∧ phaseE < rmin*mesh ∧
    0 < sourceK ∧ sourceK ≤ 1 ∧ 0 < sourceCost ∧
    12*e*((22:ℝ)+2)+8*sourceK+2*sourceCost ≤ epsw/2
  window_conditions : 0 < I ∧ (49/100:ℝ) ≤ I*e
  epsilon_conditions : 0 < eps ∧ (N+8)*eps ≤ rho
  loss_conditions : 0 < ζ ∧ 0 < μ ∧ 0 < pad ∧ 0 < normalizerLoss ∧
    0 < dyadLoss ∧ 0 < saving ∧ 0 < loss ∧ 0 < phaseCost
  geometry_conditions : ζ+μ ≤ 3/16 ∧ 13/16+ζ+2*pad ≤ 5/6 ∧ 2*pad ≤ μ
  count_budget : 159*epsw+epsm+R+7*nu+countCost ≤ 1/32
  central_budget : (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
    (26*e+(N+8)*eps+loss+mesh/6)+normalizerLoss+(saving+dyadLoss) ≤ 49/440640
  floor_budget : 2*(ζ+μ)+26*e+(N+8)*eps+loss+mesh/6+normalizerLoss+(saving+dyadLoss) ≤ 7/1200
  late_height : ∀ceiling : ℝ,0 < ceiling → ∀J : ℕ,∃heightPower logCost tau : ℝ,
    0 < heightPower ∧ 0 < logCost ∧ 0 < tau ∧
    logCost+heightPower*J ≤ (1/200)*countCost ∧
    tau < heightPower ∧ tau < (1/200)/2 ∧ 4*tau < (1/200)*sourceCost ∧
    2*tau < (1/200)*phaseCost ∧ tau*(2+4*eps) < loss ∧ tau < ceiling

/-- All real and finite slot restrictions in actual_counted_full_band have
simultaneous witnesses. The final height is chosen only after J. This is
parameter feasibility, not a proof of any analytic estimate. -/
theorem exists_actual_retained_parameters (gap : ℝ) (hgap : 0 < gap) :
    ∃p : ActualRetainedParameters,p.saving < gap := by
  obtain ⟨rho,hrho,hrhogap,hrho1⟩ := exists_actual_reserve gap hgap
  let epsm : ℝ := rho/2
  have hem : 0 < epsm := by dsimp [epsm];positivity
  have hemr : epsm ≤ rho := by dsimp [epsm];linarith
  have hem1 : epsm ≤ 1 := by linarith
  have hcommon := PhysicalDetectorUniform.commonMesh_pos 2 0 1 (epsm/2)
    (by norm_num) (by norm_num) (by positivity)
  let R : ℝ := min (rho/2) (PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2)/2)
  have hR : 0 < R := by dsimp [R];positivity
  have hRr : R ≤ rho := (min_le_left _ _).trans (by linarith)
  have hRc : R ≤ PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2) :=
    (min_le_right _ _).trans (by linarith)
  have hhalf : 0 < rho/2 := by positivity
  have hquarter : 0 < rho/4 := by positivity
  obtain ⟨N,hN,heven,ell,rmin,hrmin,hell,hellsum,hslots,_hscales⟩ :=
    PhysicalSlotSupply.exists_even_physical_slot_lengths (1/200) (5/6) (rho/2) R
      (by norm_num) (by norm_num) hhalf hR
  obtain ⟨epsw,e,phaseE,phaseK,sourceK,sourceCost,hearly⟩ :=
    actual_early_parameter_choices rho epsm R rmin (rho/2) hrho hem hR hrmin hhalf
  rcases hearly with ⟨hew,hew1,hewM,hewr,he,he1,her,hphaseE,hphaseK,hphaseBudget,hphaseGap,
    hsourceK,hsourceK1,hsourceCost,hsourceBudget⟩
  obtain ⟨eps,heps,hepsr⟩ := exists_actual_central_epsilon rho hrho N
  obtain ⟨I,hI⟩ := exists_nat_gt ((49/100:ℝ)/e)
  have hIpos : 0 < I := by
    exact_mod_cast ((div_pos (by norm_num : (0:ℝ) < 49/100) he).trans hI)
  have hwidth : (49/100:ℝ) ≤ I*e := ((div_lt_iff₀ he).mp hI).le
  have hcentral := actual_central_budget_of_small_losses N
    rho epsw epsm R (rho/2) (rho/2) (rho/4) (rho/2) e eps (rho/2) (rho/2) (rho/4) (rho/4+rho/4)
    hrho hrho1 hewr hemr hRr (by linarith) (by linarith) (by linarith) (by linarith)
    her hepsr (by linarith) (by linarith) (by linarith) (by linarith)
  have hfloor := actual_floor_budget_of_small_losses N
    rho (rho/4) (rho/2) e eps (rho/2) (rho/2) (rho/4) (rho/4+rho/4)
    hrho1 (by linarith) (by linarith) her hepsr (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨{
    N := N, I := I, ell := ell,
    rho := rho, epsm := epsm, R := R, mesh := rho/2, nu := rho/2, countCost := rho/2,
    ζ := rho/4, μ := rho/2, pad := rho/4, normalizerLoss := rho/4, dyadLoss := rho/4,
    saving := rho/4, loss := rho/2, phaseCost := rho/2,
    rmin := rmin, epsw := epsw, e := e, eps := eps,
    phaseE := phaseE, phaseK := phaseK, sourceK := sourceK, sourceCost := sourceCost,
    rho_pos := hrho, rho_small := hrho1,
    mesh_conditions := ⟨hem,hem1,hR,hhalf,hhalf,hhalf,hRc⟩,
    slot_conditions := ⟨hN,heven,hrmin,hell,hellsum,fun j=>⟨(hslots j).1,(hslots j).2.1,(hslots j).2.2.2⟩⟩,
    early_conditions := ⟨hew,hew1,hewM,hewr,he,he1,her,hphaseE,hphaseK,hphaseBudget,hphaseGap,
      hsourceK,hsourceK1,hsourceCost,hsourceBudget⟩,
    window_conditions := ⟨hIpos,hwidth⟩,
    epsilon_conditions := ⟨heps,hepsr⟩,
    loss_conditions := ⟨hquarter,hhalf,hquarter,hquarter,hquarter,hquarter,hhalf,hhalf⟩,
    geometry_conditions := ⟨hfloor.1,by linarith,by linarith⟩,
    count_budget := hcentral.1, central_budget := hcentral.2, floor_budget := hfloor.2,
    late_height := fun ceiling hceil=>exists_actual_height_budget (1/200) (rho/2) sourceCost
      (rho/2) eps (rho/2) ceiling (by norm_num) hhalf hsourceCost hhalf heps.le hhalf hceil
  },?_⟩
  change rho/4 < gap
  linarith

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_retained_parameters
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_retained_parameters
