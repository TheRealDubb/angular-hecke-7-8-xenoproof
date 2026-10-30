import AngularPhysicalSharpInputPower
import AngularPhysicalAmplifiedUniform
import OAI.NumberTheory.DirichletL.Energy.AmplifierFamilyAdmission
noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AmplifiedRadical
open AngularRowClosure ChildRows CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentAmplificationGlobal
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationErrorPool CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationChildEnergy CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationFamily
  (amplificationPhase amplificationPhase_expansion amplificationPhase_norm)
open CenteredMomentAmplificationActiveFamily (actual_error_energy_active)
local notation "O" => ActualEisensteinCubic.O
local instance angularSuccessorAmplifierAdmissionSumDecEq {ι:Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open PlainRows PlainRows.Amplification PlainRows.ChildInputs
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationEligibility CenteredMomentPrimeElements
open Filter
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale
open CenteredMomentPrimePool
open PlainRows.CommonRows PlainRows.FirstAnnularInput
open SecondSourcePower
open CenteredMomentCommonProfile CenteredMomentAmplificationAllocationCost
open CenteredMomentSecondHeightFamily
open CommonExceptionalSource (extracted_lower)
open PlainRows.AmplifiedRayDictionary
open CenteredMomentFirstPhysicalSource (fixedPresentationCost)
open CenteredMomentFirstSourceConductorCaps (rayCost)
open CenteredMomentEnergyAmplifierFamilyAdmission (referenceCost referenceCost_ge_one)
variable {α:Type*}[Fintype α]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem child_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(t Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

def parentLower (s:Input α)(Z:ℝ):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))

theorem parent_lower_scales (s:Input α)(Z:ℝ)(hZ:1<Z):
    Z^(parentLower s Z)≤s.X₁ ∧ Z^(parentLower s Z)≤s.X₂ ∧
    Z^(parentLower s Z)≤s.Y₁ ∧ Z^(parentLower s Z)≤s.Y₂:=by
  have h (X:ℝ)(hX:0<X)(hx:parentLower s Z≤Real.logb Z X):Z^(parentLower s Z)≤X:=by
    calc
      _≤Z^(Real.logb Z X):=Real.rpow_le_rpow_of_exponent_le hZ.le hx
      _=X:=Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX
  exact ⟨h _ s.X₁_pos ((min_le_left _ _).trans (min_le_left _ _)),
    h _ s.X₂_pos ((min_le_left _ _).trans (min_le_right _ _)),
    h _ s.Y₁_pos ((min_le_right _ _).trans (min_le_left _ _)),
    h _ s.Y₂_pos ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem main_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(t Z:ℝ)(hZ:1<Z):
    let d:=child s C R B τ t
    let r:=parentLower s Z-Real.logb Z (C.absNorm:ℝ)
    Z^r≤d.X₁ ∧ Z^r≤d.X₂ ∧ Z^r≤d.Y₁ ∧ Z^r≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact child_lower s C R hC B τ t Z (parentLower s Z) hZ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem active_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:AngularCharacter)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hpn:(Ideal.span {p}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hp
  have hh:=child_lower (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C)
    (pow_ne_zero k hpn) Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have he:Real.logb Z (((Ideal.span {p}:Ideal O)^k).absNorm:ℝ)=errorRemoval p Z k:=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
    rfl
  simpa only [he] using hh

theorem restored_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:AngularCharacter)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=restoredError s C R B τ t (Ideal.span {p}) k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z r hZ hX₁ hX₂ hY₁ hY₂

theorem error_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:AngularCharacter)(v Z:ℝ)(hZ:1<Z):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=parentLower s Z-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z (parentLower s Z) hZ
    h.1 h.2.1 h.2.2.1 h.2.2.2

theorem actual_error_reference_cap (ρ υ:AngularCharacter)(χ:RayFourExpansion.RayCharacter)
    (p:O)(hp:p≠0)(n:ℕ)(hn:n=0 ∨ n=5 ∨ n=6)(Z:ℝ)(hZ:1<Z)
    (hυ:υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent n)):
    (υ.modulus.absNorm:ℝ)≤referenceCost*(ρ.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (n+1)):=by
  have hray:=SecondFamily.child_modulus_bound ρ χ
  have hN:(υ.modulus.absNorm:ℝ)≤
      ((childCharacter ρ χ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)):=by
    rw [←radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ n hn]
    exact_mod_cast hυ
  have hr:((childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm:=by exact_mod_cast hray
  calc
    _≤((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        Z^(errorMoving p Z (n+1)):=by apply hN.trans;gcongr
    _=rayCost*(ρ.modulus.absNorm:ℝ)*Z^(errorMoving p Z (n+1)):=by
      unfold rayCost fixedPresentationCost;ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      exact mul_le_mul_of_nonneg_right (le_max_right 1 rayCost) (Nat.cast_nonneg _)


end OAI.SevenEighths.Angular.AmplifiedRadical

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.child_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.child_lower

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.parent_lower_scales
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.parent_lower_scales

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.main_minimum_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.main_minimum_lower

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.active_error_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.active_error_lower

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.restored_error_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.restored_error_lower

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.error_minimum_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.error_minimum_lower

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.actual_error_reference_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.actual_error_reference_cap
