import AngularPhysicalPlainChildData

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.ChildInputs
open CommonRows CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [instι:Fintype ι]
local instance angularPlainChildGeometryDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

theorem child_tuplePool (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) :
    liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 =
      Fintype.piFinset (child s C R B τ t).pools := by
  ext v
  simp only [liveBox,Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i =>
      have hi:=h (Sum.inl i)
      simpa only [remainingSets,child,commonData,Input.pools,Sum.elim_inl,live_slot_one B.val i,
        residual_one] using hi
    | inr j =>
      fin_cases j
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 0)
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 1)

theorem child_profile (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) :
    maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 = (original (child s C R B τ t) (R*C) seed).profile := by
  funext v
  simp only [maskedLiveProfile,OriginalData.profile,original,child,commonData,
    profileCoefficient,one_mul,idealRectangle_extract]
  rfl

theorem prime_slot_one (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) (i : ι) : B.val (Sum.inl i)=1 :=
  allocation_slot_one s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B i

theorem prime_slots_live (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : liveIndices B.val=Finset.univ :=
  all_slots_live s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem prime_plain_norm_product (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) :
    (B.val (Sum.inr 0)).absNorm*(B.val (Sum.inr 1)).absNorm=Q.absNorm^k := by
  rw [←map_mul,allocation_plain_product s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B,map_pow]

theorem child_products (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : AngularCharacter) (t : ℝ) :
    (child s (Q^k) R B τ t).X₁*(child s (Q^k) R B τ t).X₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k ∧
    (child s (Q^k) R B τ t).Y₁*(child s (Q^k) R B τ t).Y₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k := by
  have hnorm : ((B.val (Sum.inr 0)).absNorm:ℝ)*(B.val (Sum.inr 1)).absNorm=(Q.absNorm:ℝ)^k := by
    exact_mod_cast prime_plain_norm_product s Q hQ k hslot B
  change (s.X₁/_)*(s.X₂/_)=_ ∧ (s.Y₁/_)*(s.Y₂/_)=_
  rw [div_mul_div_comm,div_mul_div_comm,hnorm,s.same_product]
  exact ⟨rfl,rfl⟩

theorem child_volume (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : AngularCharacter) (t : ℝ) :
    volume (child s (Q^k) R B τ t)=volume s/(Q.absNorm:ℝ)^k := by
  change (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    (∏i:liveIndices B.val,s.P i.val)=_
  rw [div_mul_div_comm]
  exact remainingRaw_exact s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B s.P (s.X₁*s.X₂)

theorem child_slot_card (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : Fintype.card (liveIndices B.val)=Fintype.card ι :=
  live_slot_card s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem child_slot_scale_ge_one (s : Input ι) (hs : ∀i,1≤s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ) :
    ∀i,1≤(child s C R B τ t).P i := fun i=>hs i.val

theorem child_plain_annuli (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t a₁ a₂ b₁ b₂ : ℝ)
    (h₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (h₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) :
    Function.support (child s C R B τ t).W₁⊆Set.Icc a₁ b₁ ∧
    Function.support (child s C R B τ t).W₂⊆Set.Icc a₂ b₂ := ⟨h₁,h₂⟩


end OAI.SevenEighths.Angular.PlainRows.ChildInputs

#print axioms OAI.SevenEighths.Angular.PlainRows.ChildInputs.child_volume
#print axioms OAI.SevenEighths.Angular.PlainRows.ChildInputs.child_slot_card
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.ChildInputs.child_slot_card
