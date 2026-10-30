import AngularPhysicalAllocatedPairEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.CanonicalPaid
open EnergyState EnergyBands RelativePrime InductionEnergy PlainRows
open EnergyAllocatedChildren EnergyPaid PlainRows.CommonRows PlainRows.AllocatedRayDictionary
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
open CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedProfiles (retainedPair retained_pair_control)
open CenteredMomentEnergyAllocatedClipped (pair scale scale_pos scale_cap)
open CenteredMomentEnergyBands (length)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]

variable (M:Ideal O) [NeZero M]
local instance angularClippedPaidFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
variable (angularOrder:ℕ)
theorem actual_clipped_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:(3/4:ℝ)≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:AngularCharacter,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(ha:0<a),0≤L → ∀Q:Ideal O,Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt angularOrder (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH angularOrder W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState angularOrder Z Bmask bΦ,st.character.k=η₀.k → st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_allocated_paid_bands (α:=α) M H hH angularOrder W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild ha hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hanchor hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  rw [allocated_pair st hunit]
  exact hbound Z hZ (a/max 1 b) b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hanchor hunit hQ hs (pair D alloc ha p v X₁ X₂ hX₁ hX₂)
    (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
    (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
    (scale_cap D alloc Z L X₁ st.base_ge_one hL hX₁ hc₁ 0 F₁ hF₁)
    (scale_cap D alloc Z L X₂ st.base_ge_one hL hX₂ hc₂ 1 F₂ hF₂)

end OAI.SevenEighths.Angular.CanonicalPaid

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.actual_clipped_paid_bands
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.actual_clipped_paid_bands
