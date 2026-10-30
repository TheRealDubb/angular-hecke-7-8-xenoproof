import AngularPhysicalActiveInputEnergy

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
local instance AngularRestoredErrorSourceDecEq {β:Type*} : DecidableEq β := Classical.decEq _
def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

lemma error_source_active (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) :
    child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v=
      activeInput (restoredError s C R B τ t Q k Bp υ v) := rfl

theorem restoredError_data (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) :
    let d:=restoredError s C R B τ t Q k Bp υ v
    d.η=υ ∧ d.t=v ∧ d.m=fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k)) ∧
    d.X₁=s.X₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.X₂=s.X₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm ∧
    d.Y₁=s.Y₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.Y₂=s.Y₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem error_live_slots (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)) :
    liveIndices Bp.val=Finset.univ :=
  prime_slots_live (activeInput (child s C R B τ t)) Q hQ k hslot Bp

theorem restoredError_volume (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) :
    volume (restoredError s C R B τ t Q k Bp υ v)=
      volume s/(CenteredMomentCommonRawScale.rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  have hh:=child_volume (activeInput (child s C R B τ t)) Q hQ k hslot (R*C) Bp υ v
  rw [error_source_active,active_volume,active_volume,common_volume,div_div] at hh
  exact hh

theorem error_normalized_source (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v Φ K=
      normalizedGaussSource (restoredError s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed Φ K := by
  unfold childNormalizedGaussSource
  rw [error_source_active,active_normalized]

theorem error_normalized_sum (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (υ : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→AngularCharacter)
    (v : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp (υ Bp) (v Bp) Φ K)=
    ∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      normalizedGaussSource (restoredError s C R B τ t Q k Bp (υ Bp) (v Bp)) ((R*C)*(Q^k)) seed Φ K :=
  Finset.sum_congr rfl (fun Bp _=>error_normalized_source s C R seed B τ t Q k Bp (υ Bp) (v Bp) Φ K)

theorem error_energy (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let e:=child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v
    let d:=restoredError s C R B τ t Q k Bp υ v
    energy e.η e.m 1 0 W₁ W₂ e.slots
      (fun i=>heightCoefficient (e.toData.coefficient i) e.t) e.P X₁ X₂ keep Φ K=
    energy d.η d.m 1 0 W₁ W₂ d.slots
      (fun i=>heightCoefficient (d.toData.coefficient i) d.t) d.P X₁ X₂ keep Φ K := by
  dsimp only
  rw [error_source_active]
  exact energy_active (restoredError s C R B τ t Q k Bp υ v) υ
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k))) 1 W₁ W₂ 0 v X₁ X₂ keep Φ K

end OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_source_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_source_active

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoredError_data
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoredError_data

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_live_slots
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_live_slots

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoredError_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoredError_volume

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_normalized_source
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_normalized_source

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_normalized_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_normalized_sum

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.error_energy
