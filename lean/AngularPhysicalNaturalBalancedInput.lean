import AngularPhysicalNaturalStageMatches
import AngularPhysicalNaturalStageAdmission
import AngularPhysicalNaturalLowEntry
import AngularPhysicalNaturalLowBands
noncomputable section
set_option maxHeartbeats 600000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.NaturalStage
open PlainRows PlainRows.CommonRows PlainRows.FirstPhysical
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
variable {α:Type*}[Fintype α][DecidableEq α]
local instance successorBalancedInputDecEq : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:AngularCharacter)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def balancedInput:Input α:=
  input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches (htype:s.character.k=η₀.k):
    PlainRows.AllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  exact ⟨htype,fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl⟩

omit [DecidableEq α] in
lemma balanced_volume:
    PlainRows.CommonRows.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:(3/4:ℝ)≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width)(hs:s.width≤Mcap):
    PlainRows.CommonRows.volume balancedSource≤Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hx (X:ℝ):X≤Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)


end OAI.SevenEighths.Angular.NaturalStage

#print axioms OAI.SevenEighths.Angular.NaturalStage.balanced_matches
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.balanced_matches

#print axioms OAI.SevenEighths.Angular.NaturalStage.balanced_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.balanced_volume

#print axioms OAI.SevenEighths.Angular.NaturalStage.balanced_volume_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.balanced_volume_bound
