import AngularPhysicalDetectorHighCompensatedContinuation

/- Actual angular adaptation of pinned OAI-003 source proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (rowCharacter unitPart unitPart_spec unitPart_coprime unitPart_ne_zero
  multiplicity_lt_six canonical_decomposition markExclusions markedSourceExclusions
  marked_firstTail FirstTail selected_V_ne_zero row_phase_ramified)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

theorem continuedMarkedLocal_eq_quotient (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hV : 1-coordV P.val.absNorm z≠0) :
    continuedMarkedLocal η u P hs x w z=(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z) := by
  rw [ramifiedCorrection_eq_marked]
  field_simp
  ring

theorem continuedMarkedLocal_analyticAt_x (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : theta<x.re) (hz : (4/25:ℝ)≤z.re) :
    AnalyticAt ℂ (fun x=>continuedMarkedLocal η u P hs x w z) x := by
  have he : (fun x=>continuedMarkedLocal η u P hs x w z)=
      (fun x=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun x=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact (((ramifiedCorrection_analytic_x η u P hs hQ w z hz) x hx).sub analyticAt_const).div_const

theorem continuedMarkedLocal_differentiable_w (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : theta≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedMarkedLocal η u P hs x w z) := by
  have he : (fun w=>continuedMarkedLocal η u P hs x w z)=
      (fun w=>(ramifiedCorrection η u P hs x w z-1)/(1-coordV P.val.absNorm z)) :=
    funext (fun w=>continuedMarkedLocal_eq_quotient η u P hs x w z (selected_V_ne_zero P hQ z hz))
  rw [he]
  exact ((ramifiedCorrection_analytic_w η u P hs hQ x z hx hz).sub_const 1).div_const _

theorem continuedMarkedLocal_analyticAt_z (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : theta≤x.re) (hz : (4/25:ℝ)<z.re) :
    AnalyticAt ℂ (fun z=>continuedMarkedLocal η u P hs x w z) z := by
  have hcv := (coordV_differentiable (P.val.absNorm:ℝ) (by linarith)).analyticAt z
  have ha : AnalyticAt ℂ (fun t=>(ramifiedCorrection η u P hs x w t-1)/(1-coordV P.val.absNorm t)) z :=
    (((ramifiedCorrection_analytic_z η u P hs hQ x w hx) z hz).sub analyticAt_const).div
    (analyticAt_const.sub hcv) (selected_V_ne_zero P hQ z hz.le)
  apply ha.congr
  filter_upwards [(Complex.isOpen_re_gt (4/25)).mem_nhds hz] with t ht
  exact (continuedMarkedLocal_eq_quotient η u P hs x w t (selected_V_ne_zero P hQ t ht.le)).symm

theorem continuedCompensatedLocal_differentiableAt_x (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : theta<x.re) (hz : (4/25:ℝ)≤z.re) :
    DifferentiableAt ℂ (fun x=>continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) x := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := (continuedMarkedLocal_analyticAt_x η u P hs hQ x w z hx hz).differentiableAt
  have hD := coordD_differentiable (P.val.absNorm:ℝ) hQ0 (η.idealHom P.val) (idealRowHom u.val P.val)
  have hB : Differentiable ℂ (fun x:ℂ=>star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) :=
    (differentiable_id.const_cpow (Or.inl hQc)).const_mul _
  have hd := (remainder_open_region_denominators (P.val.absNorm:ℝ) 0 (η.idealHom P.val)
    (idealRowHom u.val P.val) x z hQ (by simp) (AngularCharacter.norm_idealHom_le_one η _)
    (idealRowHom_norm u.val _) hx.le hz).2.2
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop (disch := first | assumption | exact Or.inl hQc)

theorem continuedCompensatedLocal_differentiable_w (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : theta≤x.re) (hz : (4/25:ℝ)≤z.re) :
    Differentiable ℂ (fun w=>continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQc : (P.val.absNorm:ℂ)≠0 := by exact_mod_cast hQ0.ne'
  have hM := continuedMarkedLocal_differentiable_w η u P hs hQ x z hx hz
  have hW := coordW_differentiable (P.val.absNorm:ℝ) hQ0 (idealRowHom u.val P.val)
  have hq : Differentiable ℂ (fun w:ℂ=>(P.val.absNorm:ℂ)^(-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hQc)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop

theorem continuedCompensatedLocal_differentiableAt_z (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : theta≤x.re) (hz : (4/25:ℝ)<z.re) :
    DifferentiableAt ℂ (fun z=>continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))) z := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hM := (continuedMarkedLocal_analyticAt_z η u P hs hQ x w z hx hz).differentiableAt
  have hV := coordV_differentiable (P.val.absNorm:ℝ) hQ0
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement
  fun_prop


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedMarkedLocal_analyticAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_differentiable_w

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_differentiableAt_z
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_differentiableAt_z
