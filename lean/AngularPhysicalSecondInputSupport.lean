import AngularPhysicalSecondGaussianPower
import AngularPhysicalFirstSourceSupport
import OAI.NumberTheory.DirichletL.Moments.SecondInputCapacitySource
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.SecondSourcePower
open PlainRows PlainRows.CommonRows PlainRows.RadialEnergy ChildRows SecondFamily ChildState
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentSecondOriginalChildren (sourceRadial)
open CenteredMomentSecondPhysicalBlock (outerScalar)
open CenteredMomentSecondDyadicRowSupport (dyadicRows dyadicRows_subset dyadicRows_norm)
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg ballProfile_majorizes)
open CenteredMomentSecondHeightFamily (fixedBadMask)
open Filter
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance {κ:Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open PhysicalBlock CenteredMomentSourceLiveColumn

open SourceCapacity CenteredMomentCommonHeightEnvelope
open ConcretePrimeRowBridge
open PlainRows.SecondSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondBlockHarmonicMass CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedRatioScalar (retainedRatio)
open SecondNonexceptionalAggregate PhysicalBlock

open FiniteProfileExceptional CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open EisensteinSchwartzPoisson

open MeasureTheory UniqueFactorizationMonoid
open PlainRows.ChildInputs PlainRows.ChildSourceCaps
open CenteredMomentCommonProfile
open DetectorAmplitude (slotControl slotControl_nonneg)
open CommonExceptionalSource (frozenProfile frozenProfile_nonneg)
open FiniteProfileExceptionalPhysical (profileFactor profileFactor_nonneg)
open CenteredMomentFirstChildProfileControl (exceptionalConstant)
open CenteredMomentSecondChildPowerBudget (coefficients powers)

open CenteredMomentSecondSourcePowerDescent (physicalFactors physicalFactors_nonneg)
open CenteredMomentSecondSourceSeededPowerDescent (seededFactors)
open CenteredMomentSourceInputTailSeed (paid_seed_term)
open CenteredMomentSecondReferenceNormalization (referenceEnvelope seededFactors_rescale)
open PlainRows.Amplification PlainRows.FirstAnnularInput PlainRows.FirstSourceAdmission
open PlainRows.FirstPhysical.Support (original_column_lower)
open CenteredMomentSecondInputCapacitySource (lowerFactor)
omit [DecidableEq ι] in
lemma child_mass (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) : mass (child s C R B τ t)≤mass s := by
  change (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma child_card (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (liveIndices B))

theorem actual_lower_support (N:ℕ)(slotLower plainLower:ℝ)(hs:0<slotLower)(hp:0<plainLower)
    (s:Input ι)(hc:Fintype.card ι≤N)(hlo:slotLower≤s.lower)
    (hW₁:∀x,s.W₁ x≠0→plainLower≤x)(hW₂:∀x,s.W₂ x≠0→plainLower≤x)
    (R seed I:Ideal O)(hne:coefficient s R seed I≠0):
    lowerFactor N slotLower plainLower*volume s≤(I.absNorm:ℝ):=by
  have hm:0≤min 1 slotLower:=(lt_min zero_lt_one hs).le
  have hprod:(min 1 slotLower)^N≤∏i,s.lo i:=by
    apply (pow_le_pow_of_le_one hm (min_le_left _ _) hc).trans
    have hh:=Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _:ι=>min 1 slotLower)
      (g:=fun i=>s.lo i) (fun _ _=>hm)
      (fun i _=>(min_le_right _ _).trans (hlo.trans (s.lower_le i)))
    simpa only [Finset.prod_const,Finset.card_univ] using hh
  have hh:=original_column_lower s R seed I plainLower plainLower hp.le hp.le hW₁ hW₂ hne
  change (∏i,s.lo i)*plainLower*plainLower*volume s≤(I.absNorm:ℝ) at hh
  apply le_trans _ hh
  have hv:0≤volume s:=(volume_pos s).le
  unfold lowerFactor
  nlinarith [mul_le_mul_of_nonneg_right hprod (mul_nonneg (sq_nonneg plainLower) hv)]


end OAI.SevenEighths.Angular.SecondSourcePower

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.child_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.child_mass

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.child_card
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.child_card

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.actual_lower_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.actual_lower_support
