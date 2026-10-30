import AngularPhysicalErrorSourceAdmission
import AngularPhysicalErrorAllocationTransport
import AngularPhysicalNestedReferencePaid

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.CanonicalPaid
open EnergyState EnergyBands RelativePrime InductionEnergy PlainRows
open EnergyAllocatedChildren EnergyPaid PlainRows.CommonRows PlainRows.AllocatedRayDictionary
open AllocatedNatural AllocatedRadial NaturalRows ChildState ConcreteTraceCRT PlainRows.RadialEnergy
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos)
open CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedClipped (pair scale scale_pos scale_cap)
open CenteredMomentEnergyBands (length)
open CenteredMomentSectorLocalization (dyadicScale dyadicScale_pos)
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [instα:DecidableEq α]
variable (M:Ideal O) [NeZero M]
local instance angularCanonicalRawCapsFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
variable (angularOrder:ℕ)

open PlainRows.ChildInputs PlainRows.ChildSourceCaps PlainRows.FirstSourceAdmission
open PlainRows.FirstAnnularInput PlainRows.AmplifiedRayDictionary PlainRows.AllocatedChildCapacity
open PlainRows.FirstPhysical PhysicalBlock SecondFamily
open CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSourceLiveColumn CenteredMomentSecondCanonical
open CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstPhysicalSource (fixedPresentationCost)
open CenteredMomentFirstAmplifiedCapacityCommon (envelopeRef envelope_pos ratioPenalty)
open CenteredMomentAmplificationChildSourceCaps (norm_ge_one)
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
omit instα in
lemma common_raw_caps (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (τ:AngularCharacter)(t F:ℝ)(h₁:src.X₁≤F)(h₂:src.X₂≤F)(h₃:src.Y₁≤F)(h₄:src.Y₂≤F):
    let d:=commonData (withHeight src τ t) C R B
    d.X₁≤F ∧ d.X₂≤F ∧ d.Y₁≤F ∧ d.Y₂≤F:=by
  have hN (j:α⊕Fin 2):(1:ℝ)≤Ideal.absNorm (B.val j):=
    norm_ge_one _ (alloc_ne src C B j)
  exact ⟨(div_le_self src.X₁_pos.le (hN _)).trans h₁,
    (div_le_self src.X₂_pos.le (hN _)).trans h₂,
    (div_le_self src.Y₁_pos.le (hN _)).trans h₃,
    (div_le_self src.Y₂_pos.le (hN _)).trans h₄⟩

end OAI.SevenEighths.Angular.CanonicalPaid

#print axioms OAI.SevenEighths.Angular.CanonicalPaid.common_raw_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalPaid.common_raw_caps
