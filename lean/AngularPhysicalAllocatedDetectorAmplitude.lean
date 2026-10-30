import AngularPhysicalDetectorAmplitudeControl

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.DetectorAmplitude
open PlainRows DetectorSource ExceptionalRows CenteredMomentDetectorDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentAllocatedCenteredCapped (allocated_lower remaining_volume)
open CenteredMomentExceptionalCappedAmplitude (max_raw_reduction)
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem actual_allocated_amplitude (angularType:ℤ) (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀(s:Data ι)(Z:ℝ),s.η.k=angularType → 1<Z → (∀i,1≤s.P i) →
      ∀z:O,s.m≠0 → s.A≠0 → z≠0 → goodLambda∣s.m → (2:O)∣s.m →
      (AngularRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B →
      ExceptionalRows.FixedInducingRow s.η Q s.m s.A z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ r:ℝ,s.W₁=detectorSchwartz r₁ j σ₁ t₁ → s.W₂=detectorSchwartz r₂ k σ₂ t₂ →
      Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖amplitude s D a z‖^2≤
        (C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J*slotControl s)^2*
          (s.X₁*s.X₂*∏i,s.P i)/
          ((formalReductionFactor D a s.P)^2*(Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0))^2):=by
  obtain ⟨J,hJ⟩:=actual_detector_allocated_capped angularType ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hcap⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ s Z htype hZ hP z hm hA hz hml hm2 hcond hex D a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂
    t₁ t₂ r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hb:=hcap ι Z hZ s.η htype s.m s.A z hm hA hz hml hm2 hcond hex s.slots s.coefficient s.P
    (fun i=>max 0 (s.hi i)) s.M hP (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i))
    s.coefficient_bound (fun i I _ hi=>coefficient_support s i I hi) D a
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ s.t s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) r
    hX₁ hX₂ hY₁ hY₂ rfl s.same_product
  rw [←hW₁,←hW₂] at hb
  have ha:=allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)
  have hred:=s.reduction_pos D a
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  let V:=s.X₁*s.X₂*∏i,s.P i
  let d:=formalReductionFactor D a s.P
  let H:=C*Z^ε*(1+‖t₁‖+‖t₂‖+‖s.t‖)^J
  let F:=∏i∈frozenIndices D a,s.M i
  let L:=∏i:liveIndices D a,128*max 0 (s.hi i)*s.M i
  let M:=Z^(max (r-Real.logb Z d) 0)
  have hH:0≤H:=by dsimp [H]; positivity
  have hM:0<M:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hFL:0≤F*L:=mul_nonneg
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (zero_le_one.trans (s.M_ge_one i))))
  have hp:F*L≤slotControl s:=slot_product_bound s D a
  calc
    ‖amplitude s D a z‖^2≤F^2/d*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=ha
    _≤F^2/d*(H*L*(Real.sqrt (V/d)/M))^2:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (div_nonneg (sq_nonneg _) hred.le)
    _=(H*(F*L))^2*V/(d^2*M^2):=by
      rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (div_nonneg hraw.le hred.le)]
      dsimp only [V,d]
      field_simp [hred.ne']
    _≤(H*slotControl s)^2*V/(d^2*M^2):=by
      apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_right _ hraw.le
      exact pow_le_pow_left₀ (mul_nonneg hH hFL) (mul_le_mul_of_nonneg_left hp hH) 2
    _=_:=rfl

end OAI.SevenEighths.Angular.DetectorAmplitude

#print axioms OAI.SevenEighths.Angular.DetectorAmplitude.actual_allocated_amplitude
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorAmplitude.actual_allocated_amplitude
