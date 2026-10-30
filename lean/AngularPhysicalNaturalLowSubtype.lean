import AngularPhysicalNaturalLowBands
import AngularPhysicalEnergyReindex
import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
noncomputable section
set_option maxHeartbeats 600000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.NaturalStage
open PlainRows
open EnergyState EnergyBands InductionEnergy RelativePrime NaturalReference
open ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional CenteredMomentSourceMass
open CenteredMomentEnergyBands (length)
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyReferenceState
  (comparisonFirst comparisonSecond comparison_positive comparison_same_product)
local notation "O"=>ActualEisensteinCubic.O
variable {angularOrder:ℕ}
variable {α β:Type*}[Fintype α][Fintype β]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyBandMonotonicity (profile_control_mono)
open EnergyReindex
omit [Fintype α] [Fintype β] in
theorem positiveLowAt_embedding (angularOrder:ℕ) (e : β↪α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : AngularCharacter) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=β) M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C := by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hanchor hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  let E : T≃T.map e := Finset.equivMap e T
  let θ' : T.map e→RayQuotient.Characters M H := θ∘E.symm
  let w' : T.map e→ℝ := w∘E.symm
  let σ' : T.map e→ℝ := σ∘E.symm
  let v' : T.map e→ℝ := v∘E.symm
  have hsum : (∑i:T.map e,w' i)=∑i:T,w i := E.symm.sum_comp w
  have hh := h (T.map e) θ' w' σ' v' t height
    (fun i=>hw (E.symm i)) (fun i=>hwL (E.symm i))
    (fun i=>hσlo (E.symm i)) (fun i=>hσhi (E.symm i))
    hheight (fun i=>hv (E.symm i)) s hanchor hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
    (by rw [hsum];exact hcapacity) (by rw [hsum];exact hlow)
  have he := energy_reindex E s.character s.mask 1 (p.profile 0) (p.profile 1)
    (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
    (fun (i:T.map e) I=>(rayRelativeCharacter M H hH η₀ (θ' i)).idealHom I*
      HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
    (fun i:T.map e=>Z^(w' i)) t X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have he' : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>primePool M H bslot (Z^(w i)))
      (fun (i:T) I=>(rayRelativeCharacter M H hH η₀ (θ i)).idealHom I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:T=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T.map e=>primePool M H bslot (Z^(w' i)))
      (fun (i:T.map e) I=>(rayRelativeCharacter M H hH η₀ (θ' i)).idealHom I*
        HeckePrimeAnnular.annularWeight W (Z^(w' i)) (σ' i) (v' i) I)
      (fun i:T.map e=>Z^(w' i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
    simpa only [Function.comp_def,θ',w',σ',v',Equiv.symm_apply_apply] using he
  exact he'.le.trans hh

omit [Fintype α] in
theorem positiveLowAt_subtype (angularOrder:ℕ) (T : Finset α)
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z : ℝ)
    (η₀ : AngularCharacter) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (h : PositiveLowAt (α:=α) M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C) :
    PositiveLowAt (α:=T) M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S C :=
  positiveLowAt_embedding M H hH angularOrder ⟨Subtype.val,Subtype.val_injective⟩ W bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε κ Z η₀ Q degree S C h


end OAI.SevenEighths.Angular.NaturalStage

#print axioms OAI.SevenEighths.Angular.NaturalStage.positiveLowAt_embedding
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.positiveLowAt_embedding

#print axioms OAI.SevenEighths.Angular.NaturalStage.positiveLowAt_subtype
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.positiveLowAt_subtype
