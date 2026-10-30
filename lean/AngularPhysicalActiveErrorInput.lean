import AngularPhysicalChildEventualCaps
import AngularPhysicalFirstReferenceShift
import AngularPhysicalSecondCapacityShift
import AngularPhysicalCommonInputCapacity
import AngularPhysicalInputParentCapacity
import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacityCommon

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
local instance angularActiveErrorInputDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
def errorInput (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : AngularCharacter) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) : Input (liveIndices Bp.val) :=
  child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v

lemma active_endpoints (s : Input ι) (b b₁ b₂ : ℝ) (he : Endpoints b b₁ b₂ s) :
    Endpoints b b₁ b₂ (activeInput s) := he

theorem error_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : AngularCharacter) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : AngularCharacter) (v : ℝ) :
    let d := errorInput s C R B τ t Q k Bp υ v;
    let H := volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤sourceRadius d ∧ volume d≤geometry N b b₁ b₂*H ∧
      sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC := norm_ge_one C (allocation_ne s C B)
  have hNp : 0<(Q.absNorm:ℝ)^k := pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH : 0<volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) :=
    div_pos (volume_pos s) (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv : volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [errorInput,child_volume _ Q hQ k hslot,active_volume]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne)
      hNp.le).trans_eq (by ring)
  have hc1 := (live_card_le B.val).trans hc
  have hc2 := (live_card_le Bp.val).trans hc1
  have hep := endpoints_child b b₁ b₂ _
    (active_endpoints _ b b₁ b₂ (endpoints_child b b₁ b₂ s he C R B τ t))
    (Q^k) (R*C) Bp υ v
  have hr := radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hpow : b^N≤geometry N b b₁ b₂ := by
    have hp : 1≤b^N := one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh : 1≤b₁*b₂ := by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq (by
    unfold geometry;rw [show 2*N=N+N by omega,pow_add];ring))

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_endpoints
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.active_endpoints

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.error_caps
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.error_caps
