import AngularPhysicalActiveAllocation

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary
open CommonRows ChildInputs ChildSourceCaps FirstAnnularInput AllocatedRayDictionary
open RelativePrime InductionEnergy
open CenteredMomentSecondHeightFamily CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonMaskEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentPrimeSlot (primePool)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α]
local instance AngularActiveInputEnergyDecEq {β:Type*} : DecidableEq β := Classical.decEq _
lemma rowSlot_active (s : Input α) (i : α) (η : AngularCharacter) (m A z : O) (t v : ℝ) :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hz : s.W i ((I.absNorm:ℝ)/s.P i)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
  simp only [heightCoefficient,Data.coefficient,activeInput,hz,mul_zero,zero_mul]

lemma positive_active (s : Input α) (η : AngularCharacter) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s i η m A z t v)

theorem energy_active (s : Input α) (η : AngularCharacter) (m A : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active]

theorem positive_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : AngularCharacter) (m A z : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s (f i) η m A z t v)

theorem energy_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : AngularCharacter) (m A : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active_restrict]

theorem common_energy_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : AngularCharacter) (v : ℝ)
    (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : PlainRows.Data (liveIndices B.val) :=
      commonData (CommonRows.withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [CommonRows.withHeight, Input.pools] using B.property⟩
    let e : PlainRows.Data (liveIndices B.val) :=
      commonData (CommonRows.withHeight s τ v) C R
        ⟨B.val, by simpa only [CommonRows.withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.slots i.val)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>heightCoefficient (e.coefficient i.val) v)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.P i.val) X₁ X₂ keep Φ K := by
  exact energy_active_restrict s
    (fun i:remaining (activeInput s) C B L a J=>i.val.val) τ m A W₁ W₂ 0 v X₁ X₂ keep Φ K

end OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.rowSlot_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.rowSlot_active

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.positive_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.positive_active

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.energy_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.energy_active

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.positive_active_restrict
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.positive_active_restrict

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.energy_active_restrict
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.energy_active_restrict

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.common_energy_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.common_energy_active
