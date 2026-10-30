import AngularPhysicalNaturalTerminalMoments

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorUniform
open EnergyBands RelativePrime QuadraticInitialBound
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
local notation "O" => ActualEisensteinCubic.O

/-- A fixed numerical mesh, chosen before moduli, anchors and slot types.
The comparison is purely scalar; no zero-free seed is used. -/
def commonMesh (Mcap Bmask L ε : ℝ) : ℝ := fineMesh Mcap Bmask L (11/12) ε

theorem commonMesh_pos (Mcap Bmask L ε : ℝ) (hM : 0≤Mcap)
    (hB : 0≤Bmask) (hε : 0<ε) : 0<commonMesh Mcap Bmask L ε :=
  fineMesh_pos Mcap Bmask L (11/12) ε hM hB (by norm_num) hε

theorem commonMesh_le (Mcap Bmask L κ ε : ℝ) (hM : 0≤Mcap)
    (hB : 0≤Bmask) (hε : 0<ε) (hκ : 0≤κ) (hκhi : κ≤11/12) :
    commonMesh Mcap Bmask L ε≤fineMesh Mcap Bmask L κ ε := by
  have hr : 0≤reserve Mcap (finalSourceCap Mcap Bmask L ε) ε :=
    ((bounds Mcap (finalSourceCap Mcap Bmask L ε) κ ε hM
      (sourceCap_nonneg Mcap Bmask L hM hB _) hκ hε).2.2.2.1).le
  unfold commonMesh fineMesh mesh
  exact div_le_div_of_nonneg_left hr (by linarith) (by linarith)


end OAI.SevenEighths.Angular.PhysicalDetectorUniform

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorUniform.commonMesh_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorUniform.commonMesh_pos

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorUniform.commonMesh_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorUniform.commonMesh_le
