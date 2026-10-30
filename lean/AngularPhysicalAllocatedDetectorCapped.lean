import AngularPhysicalDetectorCappedSlots
import AngularPhysicalPlainRawEnergy
import OAI.NumberTheory.DirichletL.Moments.AllocatedCenteredCapped

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
theorem actual_detector_allocated_capped (angularType:ℤ) (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],
      ∀Z:ℝ,1<Z → ∀η:AngularCharacter,η.k=angularType → ∀m A z:O,m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (AngularRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      ExceptionalRows.FixedInducingRow η Q m A z →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b M:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀r₁ r₂:Bool,∀j k:ℕ,j≤2 → k≤2 → ∀σ₁∈Set.Icc (0:ℝ) 1,∀σ₂∈Set.Icc (0:ℝ) 1,
      ∀t₁ t₂ h X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖residualCenteredRow η m A z h S β P L a
        (detectorSchwartz r₁ j σ₁ t₁) (detectorSchwartz r₂ k σ₂ t₂) X₁ X₂ Y₁ Y₂ T‖≤
      C*Z^ε*(1+‖t₁‖+‖t₂‖+‖h‖)^J*(∏i:liveIndices L a,128*b i*M i)*
        (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
          Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)):=by
  obtain ⟨J,hJ⟩:=detector_capped_slots_uniform angularType ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  intro ι _ _ Z hZ η htype m A z hm hA hz hmLam hm2 hcond hex S β P b M hP hb hM hβ hN
    L a r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (ι:=liveIndices L a) Z hZ.le η htype m A z hm hA hz hmLam hm2 hcond hex
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>M i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hM i) (fun i=>hβ i) (fun i=>hN i)
    r₁ r₂ j k hj hk σ₁ hσ₁ σ₂ hσ₂ t₁ t₂ h
    (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end OAI.SevenEighths.Angular.DetectorAmplitude

#print axioms OAI.SevenEighths.Angular.DetectorAmplitude.actual_detector_allocated_capped
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorAmplitude.actual_detector_allocated_capped
