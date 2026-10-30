import AngularPhysicalAllocatedChildEnergy
import AngularPhysicalAllocatedPaidEnergy
import OAI.NumberTheory.DirichletL.Energy.AllocatedClipped

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
lemma allocated_pair {angularOrder:ℕ} {Z Bmask bΦ a b:ℝ}(st:NaturalState angularOrder Z Bmask bΦ)(hunit:st.puncture=1)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (ha:0<a)(p:Profiles a b)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1)) pool β P v X₁ X₂ hX₁ hX₂ F₁ F₂ J =
    energy st.character st.mask 1 0
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 0)
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 1)
      (fun i:↥(liveIndices D alloc\J)=>pool i)
      (fun i:↥(liveIndices D alloc\J)=>CenteredMomentCommonMaskEnergy.heightCoefficient (β i) v)
      (fun i:↥(liveIndices D alloc\J)=>P i)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      st.radial.keep st.radial.profile st.radial.scale:=by
  simp only [allocatedEnergy,pair,retainedPair,scale,NaturalState.mask,hunit,
    Matrix.cons_val_zero,Matrix.cons_val_one]

end OAI.SevenEighths.Angular.CanonicalPaid

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.allocated_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.allocated_pair
