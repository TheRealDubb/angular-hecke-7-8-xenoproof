import AngularPhysicalDetectorActualCountExponent
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

/-- The central reserve can be chosen below any additional positive bound,
in particular below a later fixed contradiction gap. -/
theorem exists_actual_reserve (gap : ℝ) (hg : 0<gap) :
    ∃rho : ℝ,0<rho ∧ rho<gap ∧ rho≤1/100000000 := by
  refine ⟨min gap (1/100000000)/2,by positivity,?_,?_⟩
  · have hp : 0<min gap (1/100000000:ℝ) := by positivity
    have hh := min_le_left gap (1/100000000:ℝ)
    linarith
  · have hh := min_le_right gap (1/100000000:ℝ)
    linarith

/-- One reserve controls all real losses currently exposed by the actual
class arithmetic and count. eps must be chosen after N through its displayed
(N+8)*eps bound. This does not assert the remaining contour hypotheses. -/
theorem actual_central_budget_of_small_losses (N : ℕ)
    (rho ε εm slotMesh ν countCost ζ μ e eps loss mesh overhead saving : ℝ)
    (hr : 0<rho) (hr1 : rho≤1/100000000)
    (hε : ε≤rho) (hεm : εm≤rho) (hslot : slotMesh≤rho)
    (hν : ν≤rho) (hcost : countCost≤rho) (hζ : ζ≤rho) (hμ : μ≤rho)
    (he : e≤rho) (heps : (N+8)*eps≤rho) (hl : loss≤rho)
    (hm : mesh≤rho) (ho : overhead≤rho) (hs : saving≤rho) :
    159*ε+εm+slotMesh+7*ν+countCost≤1/32 ∧
    (13/16)*(159*ε+εm+slotMesh+7*ν+countCost)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+overhead+saving≤49/440640 := by
  constructor <;> linarith

/-- The same reserve also pays the extra floor upper-scale allowance.
The normalizer loss is included once in overhead. -/
theorem actual_floor_budget_of_small_losses (N : ℕ)
    (rho ζ μ e eps loss mesh overhead saving : ℝ)
    (hr1 : rho≤1/100000000) (hζ : ζ≤rho) (hμ : μ≤rho)
    (he : e≤rho) (heps : (N+8)*eps≤rho) (hl : loss≤rho)
    (hm : mesh≤rho) (ho : overhead≤rho) (hs : saving≤rho) :
    ζ+μ≤3/16 ∧
      2*(ζ+μ)+26*e+(N+8)*eps+loss+mesh/6+overhead+saving≤7/1200 := by
  constructor <;> linarith

theorem exists_actual_central_epsilon (rho : ℝ) (hr : 0<rho) (N : ℕ) :
    ∃eps : ℝ,0<eps ∧ (N+8)*eps≤rho := by
  have hd : 0<(N:ℝ)+8 := by positivity
  refine ⟨rho/((N:ℝ)+8),div_pos hr hd,?_⟩
  rw [mul_div_cancel₀ _ hd.ne']

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_reserve

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_central_budget_of_small_losses

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_floor_budget_of_small_losses

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_central_epsilon
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_central_epsilon
