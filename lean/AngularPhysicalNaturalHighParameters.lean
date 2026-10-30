import AngularPhysicalNaturalBalancedInput
import AngularPhysicalNaturalLowPhysical
import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
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
local instance successorHighAdmissionDecEq : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:AngularCharacter)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyNaturalInputMatches (profileBound profileBound_ge_one)
local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂
lemma actual_conductor_scale (hZ:1<Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:(3/4:ℝ)≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width):
    Real.logb Z (PlainRows.CommonRows.volume balancedSource)≤s.width:=by
  have hv:0<PlainRows.CommonRows.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=>le_rfl)


end OAI.SevenEighths.Angular.NaturalStage

#print axioms OAI.SevenEighths.Angular.NaturalStage.actual_conductor_scale
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.actual_conductor_scale

#print axioms OAI.SevenEighths.Angular.NaturalStage.balanced_log_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.balanced_log_volume

#print axioms OAI.SevenEighths.Angular.NaturalStage.balanced_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalStage.balanced_control
