import AngularPhysicalLowColumn
import OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularLower
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.CanonicalUniformChildren
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
open CenteredMomentSectorLocalization (dyadicScale dyadicScale_pos normValue)
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [instα:DecidableEq α]
variable (M:Ideal O) [NeZero M]
local instance successorAnnularLowerFiniteQuotient : Finite (O⧸M) :=
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
open CanonicalPaid

open SecondSourcePower PlainRows.SecondSource
open CenteredMomentCommonProfile
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentActiveSource CenteredMomentSecondLiveBlock
open CenteredMomentSecondWindowSource RayFourExpansion Filter
open CenteredMomentSecondChildPowerBudget (coefficients powers)
open CenteredMomentSecondSourceSeededPowerDescent (seededFactors)
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonicalFrequency
open CenteredMomentSourceMass CenteredMomentSectorLocalization
open PhysicalBlock
local instance successorAnnularLowerSumDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
set_option maxHeartbeats 400000
open CenteredMomentEnergyFirstGaussianCoefficients
open CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyCanonicalAmplifiedUniform (front_mono)
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAmplifiedPowerBudget
open CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyAmplifierFamilyAdmission (referenceCost referenceCost_ge_one)
open CenteredMomentFirstPhysicalSource (fixedPresentationCost)
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic
open AmplifiedRadical
open CenteredMomentEnergyAmplifiedChildWidth (mainRadius errorRadius)
open FirstCommonSourcePower FirstColumnScalar
open CenteredMomentFirstCommonReferencePower (normalizedPower)
open CenteredMomentEnergyCanonicalLowColumn (inherited_height_split)

open CenteredMomentEnergyCanonicalAnnularLower
  (source_coefficients_mono main_powers_antitone error_powers_antitone)
lemma parent_lower_ge {ι:Type*}[Fintype ι](s:Input ι)(Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    r≤parentLower s Z:=by
  have h (x:ℝ)(hx:Z^r≤x):r≤Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

theorem actual_source_coefficients_lower {ι:Type*}[Fintype ι]
    (src:Input ι)(P:Finset (Ideal O))(C D:Ideal O)(E:Finset (CommonIndex C D))
    (K Z sigma delta reserve Mamp q deficit paid saving r:ℝ)
    (hZ:1<Z)(hsigma:0<sigma)(hMamp:0≤Mamp)
    (hX₁:Z^r≤src.X₁)(hX₂:Z^r≤src.X₂)(hY₁:Z^r≤src.Y₁)(hY₂:Z^r≤src.Y₂)
    (Hcoef:Fin 4→ℝ)(hH:∀j,0≤Hcoef j)(alpha:Fin 4→ℝ):
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Kerr:=fun p:elementPool P=>fun i:Fin 3=>errorRadius C D E K (volume src) Z sigma delta reserve p (errorIndex i+1);
    let oldr:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let newr:=r-Real.logb Z (C.absNorm:ℝ);
    ∀j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving oldr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (oldr-errorRemoval p Z (errorIndex i+1)) j) alpha j≤
    sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving newr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (newr-errorRemoval p Z (errorIndex i+1)) j) alpha j:=by
  dsimp only
  have hr:=parent_lower_ge src Z r hZ hX₁ hX₂ hY₁ hY₂
  apply source_coefficients_mono P _ (by positivity)
  · intro j
    exact mul_le_mul_of_nonneg_left (main_powers_antitone q Z _ _ _ _ _ _ _ hZ.le
      (by unfold mainRadius CenteredMomentAmplifiedRetainedRadius.mainCommonRadius;positivity)
      (sub_le_sub_right hr _) j) (hH j)
  · intro p i χ j
    exact mul_le_mul_of_nonneg_left (error_powers_antitone p (errorIndex i+1) q Z _ _ _ _ _ _ hZ.le
      (by unfold errorRadius CenteredMomentAmplifiedRetainedRadius.errorCommonRadius;positivity)
      (sub_le_sub_right (sub_le_sub_right hr _) _) j) (hH j)

theorem actual_high_annular_sum {ι:Type*}[Fintype ι]
    (src:Input ι)(P:Finset (Ideal O))(C D R:Ideal O)(E:Finset (CommonIndex C D))
    (B:actualAllocations src.pools C)(τ:AngularCharacter)(t:ℝ)
    (K Z sigma delta reserve Mamp deficit paid saving Mwidth eps:ℝ)
    (hZ:1<Z)(hsigma:0<sigma)(hMamp:0≤Mamp)
    (hX₁:Z^(Mwidth/4)≤src.X₁)(hX₂:Z^(Mwidth/4)≤src.X₂)
    (hY₁:Z^(Mwidth/4)≤src.Y₁)(hY₂:Z^(Mwidth/4)≤src.Y₂)
    (Hcoef:Fin 4→ℝ)(hH:∀j,0≤Hcoef j):
    let input:=PlainRows.ChildInputs.child src C R B τ t;
    let q:ℝ:=τ.modulus.absNorm;
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Kerr:=fun p:elementPool P=>fun i:Fin 3=>errorRadius C D E K (volume src) Z sigma delta reserve p (errorIndex i+1);
    let oldr:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let newr:=Mwidth/4-Real.logb Z (C.absNorm:ℝ);
    (∑j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving oldr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (oldr-errorRemoval p Z (errorIndex i+1)) j) (powers eps) j*
      (volume input)^(powers eps j))*mass input^2≤
    (∑j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving newr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (newr-errorRemoval p Z (errorIndex i+1)) j) (powers eps) j*
      (volume input)^(powers eps j))*mass input^2:=by
  dsimp only
  have h:=actual_source_coefficients_lower src P C D E K Z sigma delta reserve Mamp
    (τ.modulus.absNorm:ℝ) deficit paid saving (Mwidth/4) hZ hsigma hMamp hX₁ hX₂ hY₁ hY₂
    Hcoef hH (powers eps)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (h j)
    (Real.rpow_nonneg (volume_pos _).le _))


end OAI.SevenEighths.Angular.CanonicalUniformChildren

#print axioms OAI.SevenEighths.Angular.CanonicalUniformChildren.parent_lower_ge
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalUniformChildren.parent_lower_ge

#print axioms OAI.SevenEighths.Angular.CanonicalUniformChildren.actual_source_coefficients_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalUniformChildren.actual_source_coefficients_lower

#print axioms OAI.SevenEighths.Angular.CanonicalUniformChildren.actual_high_annular_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalUniformChildren.actual_high_annular_sum
