import AngularPhysicalActiveChildRestoration
import AngularPhysicalCommonInputCapacity

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.CanonicalPaid
open PlainRows.CommonRows PlainRows.FirstAnnularInput PlainRows.AmplifiedRayDictionary
open PlainRows.RadialEnergy
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [instα:DecidableEq α]
def castAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C):actualAllocations t.pools C:=
  ⟨B.val,by rw [←h];exact B.property⟩

def castDivisorAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val⊕Fin 2)):=alloc

def restoreDivisorAllocation (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val⊕Fin 2)):=alloc

lemma cast_child_energy (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight s τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight t τ v) C R (castAllocation s t h C B)) rad D
        (castDivisorAllocation s t h C B D alloc):=by
  subst t
  rfl

lemma restored_child_energy (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:AngularCharacter)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight (activeInput s) τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight s τ v) C R (restoreAllocation s C B)) rad D
        (restoreDivisorAllocation s C B D alloc):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  exact child_energy_active s C R B τ v D alloc rad

omit instα in
lemma cast_preVolume (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(v:ℝ):
    PlainRows.AllocatedChildCapacity.preVolume (commonData (withHeight t τ v) C R (castAllocation s t h C B))=
      PlainRows.AllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R B):=by
  subst t
  rfl

omit instα in
lemma cast_slot_sum (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

omit instα in
lemma restored_preVolume (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:AngularCharacter)(v:ℝ):
    PlainRows.AllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R (restoreAllocation s C B))=
      PlainRows.AllocatedChildCapacity.preVolume (commonData (withHeight (activeInput s) τ v) C R B):=rfl

omit instα in
lemma restored_slot_sum (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

end OAI.SevenEighths.Angular.CanonicalPaid

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.cast_child_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.cast_child_energy

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.restored_child_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.restored_child_energy

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.cast_preVolume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.cast_preVolume

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.cast_slot_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.cast_slot_sum

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.restored_preVolume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.restored_preVolume

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.restored_slot_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.restored_slot_sum
