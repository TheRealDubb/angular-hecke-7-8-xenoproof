import AngularPhysicalDetectorHighRowContinuation
import OAI.NumberTheory.DirichletL.PrimeRows.FirstBoundary

/- Actual angular adaptation of pinned OAI-003 source proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (unitPart unitPart_coprime multiplicity_lt_six FirstTail
  firstPrimeDefectBound firstPrimeDefectBound_nonneg rowCharacter)
local notation "O" => ActualEisensteinCubic.O

theorem unramifiedFactor_first_defect (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using firstPrimeDefectBound_nonneg eps P
  · apply unramifiedClosed_first_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact AngularCharacter.norm_idealHom_le_one η _
    · exact idealRowHom_norm u.val _
    · exact heps
    · exact hx
    · exact hz
    · exact hw
    · exact hxw

theorem unramifiedProduct_first_defect (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw) hS.half hS.small

theorem unramifiedProduct_first_multipliable (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem unramifiedProduct_first_analytic_x (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedProduct S η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply (unramifiedClosed_first_analytic_x _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (AngularCharacter.norm_idealHom_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro x hx
      change max (51/100:ℝ) (1+eps-w.re)<x.re at hx
      have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
      change (1/2:ℝ)<x.re
      linarith
  · intro P x hx
    have hx' := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
    have hxw := (lt_of_le_of_lt (le_max_right (51/100:ℝ) (1+eps-w.re)) hx)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx'.le hz hw (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_w (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedProduct S η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      exact (unramifiedClosed_first_analytic_w _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (AngularCharacter.norm_idealHom_le_one η _) (idealRowHom_norm u.val _) (by linarith) (by linarith)).mono
          (Set.subset_univ _)
  · intro P w hw
    have hw' := (lt_of_le_of_lt (le_max_left (-(1/100:ℝ)) (1+eps-x.re)) hw)
    have hxw := (lt_of_le_of_lt (le_max_right (-(1/100:ℝ)) (1+eps-x.re)) hw)
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw'.le (by linarith)
  · exact hS.half

theorem unramifiedProduct_first_analytic_z (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedProduct S η u x w z) {z : ℂ | (17/50:ℝ)<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ=>if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(1:ℂ)) _)
    · simp only [ite_eq_right h]
      apply (unramifiedClosed_first_analytic_z _ _ _ _ _ _
        (by exact_mod_cast hS.norm_four P.val P.property) (actualAPhase_norm_le_one η _)
        (AngularCharacter.norm_idealHom_le_one η _) (idealRowHom_norm u.val _) (by linarith)).mono
      intro z hz
      change (17/50:ℝ)<z.re at hz
      change (1/3:ℝ)<z.re
      linarith
  · intro P z hz
    exact unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz.le hw hxw
  · exact hS.half

theorem ramifiedCorrection_first_analytic_x (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (1/3 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | 1/2<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_first_analytic_w (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : (1/2 : ℝ)≤x.re) (hz : (1/3 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_first_analytic_z (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : (1/2 : ℝ)≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 1/3<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_first_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

theorem ramifiedCorrection_first_bound (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (51/100 : ℝ)≤x.re) (hw : -(1/100 : ℝ)≤w.re) (hz : (17/50 : ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_first_region_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz hxw _ (multiplicity_lt_six u p hp)

theorem ramified_product_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : AngularCharacter) (u : FreeRow) (x w z : ℂ),
      (51/100 : ℝ)≤x.re → -(1/100 : ℝ)≤w.re → (17/50 : ℝ)≤z.re → 1≤x.re+w.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz hxw
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_first_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz hxw
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

theorem continuedCorrection_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      1+eps≤x.re+w.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_first_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro eps S hS hfirst η u x w z hx hw hz hxw
  have hR := hbound S hS η u x w z hx hw hz (by linarith [hfirst.positive])
  have hU := unramifiedProduct_first_defect eps S hfirst η u x w z hx hz hw hxw
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_first_analytic_x (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (w z : ℂ)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x=>continuedCorrection S hS η u x w z)
      {x : ℂ | max (51/100:ℝ) (1+eps-w.re)<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_x eps S hfirst η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    w z (by linarith)).mono
  intro x hx
  change max (51/100:ℝ) (1+eps-w.re)<x.re at hx
  have hh := (lt_of_le_of_lt (le_max_left (51/100:ℝ) (1+eps-w.re)) hx)
  change (1/2:ℝ)<x.re
  linarith

theorem continuedCorrection_first_analytic_w (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w=>continuedCorrection S hS η u x w z)
      {w : ℂ | max (-(1/100:ℝ)) (1+eps-x.re)<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_w eps S hfirst η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_first_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x z (by linarith) (by linarith)).differentiableOn.analyticOnNhd (Complex.isOpen_re_gt _)

theorem continuedCorrection_first_analytic_z (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    AnalyticOnNhd ℂ (fun z=>continuedCorrection S hS η u x w z) {z : ℂ | (17/50:ℝ)<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_first_analytic_z eps S hfirst η u x w hx hw hxw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  apply (ramifiedCorrection_first_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2)
    x w (by linarith)).mono
  intro z hz
  change (17/50:ℝ)<z.re at hz
  change (1/3:ℝ)<z.re
  linarith


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_first_subpower

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_first_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_first_analytic_w

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_first_analytic_z
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_first_analytic_z
