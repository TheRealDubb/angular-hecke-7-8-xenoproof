import AngularPhysicalActiveErrorCapacity

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission
open CommonRows ChildInputs ChildSourceCaps FirstAnnularInput AllocatedChildCapacity FirstPhysical
open FirstReferenceCapacity SourceCapacity PhysicalBlock SecondFamily InputParentCapacity
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationChildSourceCaps (geometry geometry_ge_one norm_ge_one live_card_le)
open CenteredMomentFirstPhysicalSource (fixedPresentationCost fixedPresentationCost_pos)
open CenteredMomentSecondCapacitySourceShift (adjustedEnvelopeRef)
open CenteredMomentEnergyBands (length)
open CenteredMomentFirstAmplifiedCapacityCommon (envelopeRef envelope_pos ratioPenalty adjusted_log)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance AngularActiveErrorAffineDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem active_error_slot_logs_le (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      ∑i,Real.logb Z (s.P i) := by
  have hp : ∀i,1≤(activeInput (child s C R B τ t)).P i := fun i=>hP i.val
  have hs := common_slot_logs_le (activeInput (child s C R B τ t)) (Q^k) Bp Z hZ hp
  exact hs.trans (common_slot_logs_le s C B Z hZ hP)

theorem active_error_parent_affine (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v Z κ M : ℝ) (hZ : 1<Z) (hκ : 1/6≤κ) (hP : ∀i,1≤s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M) :
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤M := by
  have hh := input_affine_capacity s Z κ M hZ hcap
  have hs := active_error_slot_logs_le s C R B τ t Q k Bp υ v Z hZ hP
  have hm := mul_le_mul_of_nonneg_left hs (by linarith : 0≤6*κ-1)
  linarith

theorem active_error_raw_affine (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v Z κ M : ℝ) (hZ : 1<Z) (hκ : 1/6≤κ) (hP : ∀i,1≤s.P i)
    (hcap : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M) :
    Real.logb Z (volume (errorInput s C R B τ t Q k Bp υ v))+(6*κ-1)*
      (∑i,Real.logb Z ((errorInput s C R B τ t Q k Bp υ v).P i))≤
      M-Real.logb Z (rawReduction B.val s.P)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ) := by
  have hh := active_error_parent_affine s C R B τ t Q k Bp υ v Z κ M hZ hκ hP hcap
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hq : 0<(Q.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  rw [active_error_volume s C R B τ t Q hQ k hslot Bp υ v,
    Real.logb_div (volume_pos s).ne' (mul_pos hr (pow_pos hq k)).ne',
    Real.logb_mul hr.ne' (pow_pos hq k).ne',Real.logb_pow]
  linarith

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_error_slot_logs_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_error_slot_logs_le

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_error_parent_affine
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_error_parent_affine

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_error_raw_affine
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_error_raw_affine
