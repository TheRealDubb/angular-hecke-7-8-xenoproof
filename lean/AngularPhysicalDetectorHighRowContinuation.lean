import AngularPhysicalDetectorHighRowBounds

/- Adapted from pinned original OAI-003 proofs. Original OpenAI and
predecessor Apache-2.0 notices are retained in the pinned source tree. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (unitPart unitPart_spec unitPart_coprime unitPart_ne_zero
  multiplicity_lt_six canonical_decomposition)
local notation "O" => ActualEisensteinCubic.O

def unramifiedFactor (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal O)) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

theorem unramifiedFactor_defect (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ)
    (hx : theta≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedFactor η u P x w z-1‖≤globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply remainder_unramified_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact AngularCharacter.norm_idealHom_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz

theorem unramifiedProduct_defect (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : theta≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem unramifiedProduct_multipliable (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : theta≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem unramifiedProduct_analytic_x (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : AngularCharacter) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>unramifiedProduct S η u x w z) {x : ℂ | theta<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply remainder_unramifiedClosed_analytic_x
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact AngularCharacter.norm_idealHom_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hz
  · intro P x hx
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem unramifiedProduct_analytic_w (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : AngularCharacter) (u : FreeRow) (x z : ℂ) (hx : theta≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>unramifiedProduct S η u x w z) {w : ℂ | 9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply remainder_unramifiedClosed_analytic_w
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact AngularCharacter.norm_idealHom_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
      · exact hz
  · intro P w hw
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem unramifiedProduct_analytic_z (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : AngularCharacter) (u : FreeRow) (x w : ℂ) (hx : theta≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>unramifiedProduct S η u x w z) {z : ℂ | 4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ => if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [ite_eq_right h]
      apply remainder_unramifiedClosed_analytic_z
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact AngularCharacter.norm_idealHom_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
  · intro P z hz
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

section
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})
lemma ramifiedClosed_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|theta<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := remainder_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : theta≤x.re) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := remainder_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : theta≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := remainder_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end

lemma actualACube_norm_le (η : AngularCharacter) (p : O) : ‖actualACube η p‖≤1 := by
  have h := actualAPhase_norm_le_one η p
  rw [←actualACube_sq,norm_pow] at h
  nlinarith [norm_nonneg (actualACube η p)]

theorem ramifiedCorrection_analytic_x (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (w z : ℂ) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>ramifiedCorrection η u P hs x w z) {x : ℂ | theta<x.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_x
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hz

theorem ramifiedCorrection_analytic_w (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x z : ℂ)
    (hx : theta≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    Differentiable ℂ (fun w =>ramifiedCorrection η u P hs x w z) := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_w
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx
  · exact hz

theorem ramifiedCorrection_analytic_z (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w : ℂ) (hx : theta≤x.re) :
    AnalyticOnNhd ℂ (fun z =>ramifiedCorrection η u P hs x w z) {z : ℂ | 4/25<z.re} := by
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold ramifiedCorrection
  apply ramifiedClosed_analytic_z
  · simpa only [span_primaryGenerator_of_supported P.val hs] using hQ
  · exact actualACube_norm_le η _
  · exact hx

def ramifiedProduct (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏ P∈(ramifiedPrimes S u).attach,ramifiedCorrection η u P.val
    (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z

def continuedCorrection (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ramifiedProduct S hS η u x w z*unramifiedProduct S η u x w z

theorem continuedCorrection_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : AngularCharacter) (u : FreeRow) (x w z : ℂ),
      theta≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := ramified_product_subpower ε hε
  refine ⟨C*(3/2),by positivity,?_⟩
  intro S hS η u x w z hx hw hz
  have hR := hbound S hS η u x w z hx hw hz
  have hU := unramifiedProduct_defect S hS.tail η u x w z hx (by linarith) (by linarith)
  have hnorm : ‖unramifiedProduct S η u x w z‖≤3/2 := by
    have hh := norm_add_le (unramifiedProduct S η u x w z-1) (1 : ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    linarith
  rw [continuedCorrection,norm_mul]
  apply (mul_le_mul hR hnorm (norm_nonneg _) (by positivity)).trans
  exact le_of_eq (by ring)

theorem continuedCorrection_analytic_x (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>continuedCorrection S hS η u x w z) {x : ℂ | theta<x.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_x S hS.tail η u w z hw hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_x η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) w z hz

theorem continuedCorrection_analytic_w (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x z : ℂ) (hx : theta≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>continuedCorrection S hS η u x w z) {w : ℂ | 9/10<w.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_w S hS.tail η u x z hx hz)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact (ramifiedCorrection_analytic_w η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x z hx hz).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt _)

theorem continuedCorrection_analytic_z (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w : ℂ) (hx : theta≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>continuedCorrection S hS η u x w z) {z : ℂ | 4/25<z.re} := by
  apply AnalyticOnNhd.mul _ (unramifiedProduct_analytic_z S hS.tail η u x w hx hw)
  apply Finset.analyticOnNhd_fun_prod
  intro P hP
  exact ramifiedCorrection_analytic_z η u P.val _
    (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w hx


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_subpower

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_analytic_w

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_analytic_z
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_analytic_z
