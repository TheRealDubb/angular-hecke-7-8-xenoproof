import AngularPhysicalDetectorActualMixedMargins
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

/-- The actual count has kappa=3/4. There is no Delta/4 capacity penalty.
countCost pays the full common profile/height and label/dyadic prefactor. -/
def actualAdaptiveRowExponent (δ q ε εm slotMesh ν countCost : ℝ) : ℝ :=
  if δ≤5/6 then
    Endpoint.balancedRowCount δ (1/2-q/δ)+159*ε+εm+slotMesh+7*ν+countCost
  else 1-δ+78*ε+εm+countCost

theorem actual_adaptive_mixed_saving (N : ℕ)
    (a q ε εm slotMesh ν countCost ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2<a) (ha' : a≤1) (hq : 0≤q) (hq' : q≤(2*a-1)/2)
    (hε : 0≤ε) (hεm : 0≤εm) (hslot : 0≤slotMesh) (hν : 0≤ν) (hcost : 0≤countCost)
    (hcount : 159*ε+εm+slotMesh+7*ν+countCost≤1/32)
    (hζ : 0≤ζ) (hζ' : ζ≤3/16) (hv : v≤13/16+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤e) (heps : 0≤eps)
    (hbudget : (13/16)*(159*ε+εm+slotMesh+7*ν+countCost)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+overhead+saving≤49/440640) :
    mixedSourceExponent a v d (actualAdaptiveRowExponent (2*a-1) q ε εm slotMesh ν countCost) q+
      ProbeCentralExponent.realLoss N v e eps loss mesh+overhead≤3/16-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν+countCost := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr := ProbeCentralExponent.realLoss_bound N v e eps loss mesh (by linarith) he heps
  by_cases hd : 2*a-1≤5/6
  · have hb := balanced_mixed_saving (2*a-1) (q/(2*a-1)) 0
      (159*ε+εm+slotMesh+7*ν+countCost) ζ μ v d
      (ProbeCentralExponent.realLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx' (by norm_num) (by norm_num) hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    simpa only [actualAdaptiveRowExponent,if_pos hd,zero_div,add_zero,add_assoc] using hb
  · have hhl : 0≤78*ε+εm+countCost := by positivity
    have hh := high_mixed_margin (2*a-1) q 0 (78*ε+εm+countCost) ζ μ v d
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq' hhl (by linarith)
      hζ hv hμ hdv
    rw [haeq] at hh
    simp only [actualAdaptiveRowExponent,if_neg hd]
    simp only [add_assoc] at hh ⊢
    linarith

lemma central_class_exponent_identity (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) :
    ((25/48)*a-181/300+(105/8)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6)=
    mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh+overhead := by
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_adaptive_mixed_saving

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.central_class_exponent_identity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.central_class_exponent_identity
