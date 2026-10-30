import AngularPhysicalPaidRemainingEnergy
import AngularPhysicalStateCapacityThreeQuarters

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.EnergyPaid
open EnergyState EnergyBands RelativePrime InductionEnergy PlainRows
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]
variable (M:Ideal O) [NeZero M]
local instance angularPaidRemovalFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
variable (angularOrder:ℕ)
theorem actual_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:(3/4:ℝ)≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:AngularCharacter,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt angularOrder (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(J:Finset α)(w σ v:α→ℝ)(t height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|v i|≤height) →
    ∀s:NaturalState angularOrder Z Bmask bΦ,s.character.k=η₀.k → s.puncture=1 → s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:J=>primePool M H bslot (Z^(w i)))
      (fun (i:J) I=>(rayRelativeCharacter M H hH η₀ (θ i)).idealHom I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:J=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^(dc+degree)*
        Z^(s.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess J w (length Z X₁) (length Z X₂) s.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hrem⟩:=actual_state_capacity_removal_of_three_quarters (ι:=α) (angularOrder:=angularOrder) M H hH
    (fun _=>W) (fun _=>aslot) (fun _=>bslot) (fun _=>ha) (fun _=>hWs) (fun _=>hW)
    Mcap bΦ (2*Mcap+1) Lslot εremove lo hi hbΦ (by linarith) hLs hε
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hrem⟩:=hrem (fun i=>rayRelativeCharacter M H hH η₀ (θ i))
  have hrem := hrem κ hκ

  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    J w σ v t height mesh hmesh hw hwm hwL hσlo hσhi hheight hv s hanchor hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hrem J w (length Z X₁) (length Z X₂)
    s.width mesh hmesh hw hwm hwL
  have hrow:s.rowWidth≤Mcap:=by
    have hc:=s.character_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have hq:Mcap+s.characterWidth+1≤2*Mcap+1:=by
    have hr:=s.row_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have he:=henergy Z hZ Bmask s
    (fun i=>ray_inverse_anchor_cancels_type M H hH η₀ s.character hanchor (θ i)) hunit hrow s.characterWidth s.modulus_bound hq (internalQ Q η₀) hQ
    (inf_le_left.trans hQM) (fun i=>internalQ_le_relative_modulus M H hH Q hQM η₀ (θ i))
    σ v t height hσlo hσhi hheight hv (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
  dsimp only at he
  have hb:=remaining_energy_bound M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi Mcap εchild κ Z
    η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height
    hw hwL hσlo hσhi hheight hv s hanchor hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  apply he.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_)
  simp only [pow_add,Real.rpow_add hZp]
  ring

end OAI.SevenEighths.Angular.EnergyPaid

#print axioms OAI.SevenEighths.Angular.EnergyPaid.actual_paid_bands
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyPaid.actual_paid_bands
