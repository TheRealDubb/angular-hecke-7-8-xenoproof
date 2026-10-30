import AngularPhysicalRestoredErrorSource

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
local instance AngularAmplifiedRayMatchesDecEq {β:Type*} : DecidableEq β := Classical.decEq _
section Ray
variable (M : Ideal O) [NeZero M]
local instance angularAmplifiedRayMatchFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : AngularCharacter} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

theorem matches_child (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) (hτ:τ.k=η₀.k) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
      (fun i=>freq i.val) W bslot Z := by
  constructor
  · exact hτ
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

theorem matches_twiceChild (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : AngularCharacter) (v : ℝ)
    (hτ:τ.k=η₀.k) (hυ:υ.k=η₀.k) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t hτ) (Q^k) (R*C) Bp υ v hυ

theorem active_common_ray_energy (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (τ : AngularCharacter) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : PlainRows.Data (liveIndices B.val) :=
      commonData (CommonRows.withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [CommonRows.withHeight, Input.pools] using B.property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>primePool M H bslot (Z^(w i)))
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>fun I=>
        (rayRelativeCharacter M H hH η₀ (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>Z^(w i)) X₁ X₂ keep Φ K :=
  (common_energy_active s C R B τ v L a J m A W₁ W₂ X₁ X₂ keep Φ K).trans
    (common_energy h τ v C R (restoreAllocation s C B) L a J m A W₁ W₂ X₁ X₂ keep Φ K)

theorem restoredError_matches (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) (hτ:τ.k=η₀.k) (hυ:υ.k=η₀.k) :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_twiceChild M H hH h C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v hτ hυ

end Ray
end OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.matches_child
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.matches_child

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.matches_twiceChild
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.matches_twiceChild

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.active_common_ray_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.active_common_ray_energy

#print axioms OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoredError_matches
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.AmplifiedRayDictionary.restoredError_matches
