import AngularPhysicalDetectorActualCountBudget
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

/-- Fix every real loss first, then the actual finite profile degree J.
This supplies a positive height exponent meeting all exposed count, witness
and central-prime height restrictions. ceiling accommodates additional
already-fixed upper bounds. No analytic estimate or zero-free claim occurs
in this choice lemma. -/
theorem exists_actual_height_budget
    (dmin countCost sourceHeightCost phaseCost eps loss ceiling : ℝ)
    (hdmin : 0<dmin) (hc : 0<countCost) (hs : 0<sourceHeightCost)
    (hp : 0<phaseCost) (heps : 0≤eps) (hloss : 0<loss) (hceil : 0<ceiling) :
    ∀J : ℕ,∃heightPower logCost tau : ℝ,
      0<heightPower ∧ 0<logCost ∧ 0<tau ∧
      logCost+heightPower*J≤dmin*countCost ∧
      tau<heightPower ∧ tau<dmin/2 ∧ 4*tau<dmin*sourceHeightCost ∧
      2*tau<dmin*phaseCost ∧ tau*(2+4*eps)<loss ∧ tau<ceiling := by
  intro J
  let heightPower : ℝ := dmin*countCost/(4*((J:ℝ)+1))
  let logCost : ℝ := dmin*countCost/4
  have hh : 0<heightPower := by dsimp [heightPower];positivity
  have hlog : 0<logCost := by dsimp [logCost];positivity
  have hden : 0<2+4*eps := by positivity
  let B : ℝ := min heightPower (min (dmin/2) (min (dmin*sourceHeightCost/4)
    (min (dmin*phaseCost/2) (min (loss/(2+4*eps)) ceiling))))
  have hB : 0<B := by dsimp [B];positivity
  let tau : ℝ := B/2
  have ht : 0<tau := by dsimp [tau];positivity
  have htB : tau<B := by dsimp [tau];linarith
  have hhJ : heightPower*(J:ℝ)≤dmin*countCost/4 := by
    have hd : 4*((J:ℝ)+1)≠0 := by positivity
    have hprod : heightPower*((J:ℝ)+1)=dmin*countCost/4 := by
      dsimp [heightPower];field_simp
    nlinarith
  have ht1 : tau<heightPower := htB.trans_le (min_le_left _ _)
  have ht2 : tau<dmin/2 := htB.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : tau<dmin*sourceHeightCost/4 :=
    htB.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht4 : tau<dmin*phaseCost/2 :=
    htB.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have ht5 : tau<loss/(2+4*eps) :=
    htB.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have ht6 : tau<ceiling :=
    htB.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨heightPower,logCost,tau,hh,hlog,ht,?_,ht1,ht2,?_,?_,?_,ht6⟩
  · dsimp only [logCost];nlinarith [mul_pos hdmin hc]
  · linarith
  · linarith
  · exact (lt_div_iff₀ hden).mp ht5

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_height_budget
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_height_budget
