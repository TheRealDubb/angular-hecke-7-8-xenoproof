import AngularPhysicalFixedRayAnchor
import AngularPhysicalPlainInductionEnergy
import AngularPhysicalCommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary
open CommonRows RelativePrime InductionEnergy
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentRetainedProfile HeckePrimeAnnular
open CenteredMomentCommonMaskEnergy (heightCoefficient)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]
def originalEmbedding (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

lemma projection_injective (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Function.Injective (fun i : remaining s C B L a J => i.val.val) := by
  intro i j h
  exact Subtype.ext (Subtype.ext h)

lemma mem_originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) (i : α) :
    i ∈ originalImage s C B L a J ↔
      ∃ j ∈ remaining s C B L a J, j.val = i := by
  simp only [originalImage, Finset.mem_map, originalEmbedding, Function.Embedding.coeFn_mk]

lemma originalImage_card (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    (originalImage s C B L a J).card = (remaining s C B L a J).card := Finset.card_map _

def commonFirst (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₁ else (commonData s C R B).Y₁

def commonSecond (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₂ else (commonData s C R B).Y₂

omit [DecidableEq α] in
lemma commonFirst_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonFirst s C R B left := by
  unfold commonFirst
  split
  · exact (commonData s C R B).X₁_pos
  · exact (commonData s C R B).Y₁_pos

omit [DecidableEq α] in
lemma commonSecond_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonSecond s C R B left := by
  unfold commonSecond
  split
  · exact (commonData s C R B).X₂_pos
  · exact (commonData s C R B).Y₂_pos

end OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.projection_injective
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.projection_injective

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.mem_originalImage
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.mem_originalImage

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.originalImage_card
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.originalImage_card

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.commonFirst_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.commonFirst_pos

#print axioms OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.commonSecond_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AllocatedRayDictionary.commonSecond_pos
