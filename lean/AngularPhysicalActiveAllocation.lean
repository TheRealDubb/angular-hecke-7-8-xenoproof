import AngularPhysicalChildEventualCaps
import AngularPhysicalAllocatedRayEnergy

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
local instance AngularActiveAllocationDecEq {β:Type*} : DecidableEq β := Classical.decEq _
lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=>h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

lemma restoreAllocation_injective (s : Input α) (C : Ideal O) :
    Function.Injective (restoreAllocation s C) := by
  intro B D h
  exact Subtype.ext (congrArg (fun x : actualAllocations s.pools C=>x.val) h)

lemma child_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : AngularCharacter) (t : ℝ) :
    child (activeInput s) C R B τ t=
      activeInput (child s C R (restoreAllocation s C B) τ t) := rfl

lemma active_coefficient (s : Input α) (i : α) :
    (activeInput s).toData.coefficient i=s.toData.coefficient i := rfl

end OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.active_pools_subset
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.active_pools_subset

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.actualAllocations_mono
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.actualAllocations_mono

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoreAllocation_val
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoreAllocation_val

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoreAllocation_injective
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoreAllocation_injective

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.child_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.child_active

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.active_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.active_coefficient
