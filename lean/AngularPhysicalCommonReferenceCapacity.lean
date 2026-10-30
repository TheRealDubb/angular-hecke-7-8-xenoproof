import AngularPhysicalActiveErrorAffine
import AngularPhysicalCommonHeightEnvelope

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
local instance AngularCommonReferenceCapacityDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem common_raw_reference_shift (s:Input ι)(υ:AngularCharacter)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (B:actualAllocations s.pools C)(hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) C R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) C R0 B υ t hB
  have hc:=norm_pos C hC.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s C R0 B υ t)) hu
  have hb:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) C R0 B)=volume (child s C R0 B υ t):=rfl
  rw [he]
  linarith

theorem common_raw_reference_shift_right (s:Input ι)(υ:AngularCharacter)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (B:actualAllocations s.pools D)(hB:frozenCoefficient B.val D R0 s.ν s.W s.P≠0)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (K a Z qref:ℝ)(n:Fin 4→ℤ)(hq:0<qref)(hK:0<K)(ha:0<a)(hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*volume s≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C D hC hD U R rows W K n≠0):
    Real.logb Z (preVolume (commonData (withHeight s υ t) D R0 B))-
      Real.logb Z (envelopeRef qref C D U n)≤
      Real.logb Z K-Real.logb Z qref-Real.logb Z (volume s)+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
        (Fintype.card ι:ℝ)*Real.logb Z (max 1 s.upper)+Real.logb Z (ratioPenalty n) := by
  have hg:=actual_capacity_shift_reference_right υ t S β C D hC hD hCD U R rows W K
    (volume s) a Z qref n hq hK (volume_pos s) ha hZ hlower hne
  have hu:=common_volume_le (Fintype.card ι) (max 1 s.upper) (le_max_left _ _) s
    le_rfl (le_max_right _ _) D R0 B υ t hB
  have hc:=norm_pos D hD.1
  have hl:=Real.logb_le_logb_of_le hZ (volume_pos (child s D R0 B υ t)) hu
  have hb:0<max 1 s.upper:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.logb_div (mul_pos (pow_pos hb _) (volume_pos s)).ne' hc.ne',
    Real.logb_mul (pow_pos hb _).ne' (volume_pos s).ne',Real.logb_pow] at hl
  rw [adjusted_log Z qref hq C D hC U n,Real.logb_div (volume_pos s).ne' hc.ne'] at hg
  have he:preVolume (commonData (withHeight s υ t) D R0 B)=volume (child s D R0 B υ t):=rfl
  rw [he]
  linarith

theorem actual_width_le_reference {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→AngularCharacter}
    (hf:Family η C D hC hD U τ)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤qref)(hZ:1<Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z ((τ χ).modulus.absNorm:ℝ)+Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (envelopeRef qref C D U n) := by
  have hqpos:=norm_pos (τ χ).modulus (τ χ).modulus_ne_bot
  have he:=family_child_envelope hf t S β R rows W K hK n hne χ
  have hb:childEnvelope η C D U n≤envelopeRef qref C D U n:=by
    unfold childEnvelope envelopeRef
    gcongr
    exact (dyadicScale_pos _).le
  have hh:=Real.logb_le_logb_of_le hZ (mul_pos hqpos (dyadicScale_pos _)) (he.trans hb)
  rwa [Real.logb_mul hqpos.ne' (dyadicScale_pos _).ne'] at hh

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_raw_reference_shift
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_raw_reference_shift

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_raw_reference_shift_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_raw_reference_shift_right

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_width_le_reference
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_width_le_reference
