import AngularPhysicalAllocatedDataCapacity

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity
open CommonRows CommonMask AllocatedNatural
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentAllocatedChildCapacity
  (plainLogs remainingLogs clippingLoss clipped_pair_log clipping_loss_bound excess_le raw_volume)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem common_preVolume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    preVolume (commonData s C R B)=preVolume s.toData/
      CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hr := CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  simpa only [preVolume,commonData,div_mul_div_comm,
    CenteredMomentCommonRawScale.remainingRaw,CenteredMomentCommonRawScale.plainNorm] using
      CenteredMomentCommonRawScale.raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P

omit [DecidableEq ι] in
lemma common_reduction_ge_one (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) (hP : ∀i,1≤s.P i) :
    1≤CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hn (j : ι⊕Fin 2) : (1:ℝ)≤Ideal.absNorm (B.val j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))
  apply one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hn (Sum.inr 0)) (hn (Sum.inr 1)))
  apply Finset.one_le_prod₀
  intro i _
  unfold CenteredMomentCommonRawScale.frozenScale
  split_ifs
  · exact le_rfl
  · exact hP i

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=>Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

theorem common_allocated_raw_volume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2))) :
    let v := commonData s C R B
    let result := preVolume s.toData/(CenteredMomentCommonRawScale.rawReduction B.val s.P*
      formalReductionFactor D a v.P)
    rawScale D a v.X₁ 0*rawScale D a v.X₂ 1*(∏i∈liveIndices D a,v.P i)=result ∧
      rawScale D a v.Y₁ 0*rawScale D a v.Y₂ 1*(∏i∈liveIndices D a,v.P i)=result := by
  dsimp only
  have hx := raw_volume D a (commonData s C R B).X₁ (commonData s C R B).X₂
    (commonData s C R B).P (commonData s C R B).P_pos
  have hy := raw_volume D a (commonData s C R B).Y₁ (commonData s C R B).Y₂
    (commonData s C R B).P (commonData s C R B).P_pos
  change _=preVolume (commonData s C R B)/_ at hx
  rw [common_preVolume s C R B,div_div] at hx
  rw [(commonData s C R B).same_product] at hy
  change _=preVolume (commonData s C R B)/_ at hy
  rw [common_preVolume s C R B,div_div] at hy
  exact ⟨hx,hy⟩

theorem common_paired_capacity (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let v := commonData s C R B
    let bound := max (Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a v.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.X₁ v.X₂≠0 →
      max (plainLogs D a Z v.X₁ v.X₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.Y₁ v.Y₂≠0 →
      max (plainLogs D a Z v.Y₁ v.Y₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) := by
  dsimp only
  obtain ⟨hx,hy⟩ := paired_capacity (commonData s C R B) D a Z κ M hZ hκ (fun i=>hP i)
  have hv : Real.logb Z (preVolume (commonData s C R B))=
      Real.logb Z (preVolume s.toData)-Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P) := by
    rw [common_preVolume s C R B,Real.logb_div (preVolume_pos s.toData).ne'
      (CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos).ne']
  have hl := mul_le_mul_of_nonneg_left (common_slot_logs_le s C B Z hZ hP)
    (by linarith : 0≤6*κ-1)
  have hb : max (Real.logb Z (preVolume (commonData s C R B))-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z ((commonData s C R B).P i))+
      Real.logb Z (max 1 (commonData s C R B).b₁*max 1 (commonData s C R B).b₂)) 0≤
      max (Real.logb Z (preVolume s.toData)-
        Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
        Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
        (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0 := by
    rw [hv]
    apply max_le_max _ le_rfl
    change _≤Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    dsimp only [commonData]
    linarith
  exact ⟨fun z hz=>(hx z hz).trans hb,fun z hz=>(hy z hz).trans hb⟩

end OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_preVolume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_preVolume

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_reduction_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_reduction_ge_one

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_slot_logs_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_slot_logs_le

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_allocated_raw_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_allocated_raw_volume

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_paired_capacity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedChildCapacity.common_paired_capacity
