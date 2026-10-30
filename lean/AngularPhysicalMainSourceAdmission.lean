import AngularPhysicalCommonReferenceCapacity

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
local instance angularMainSourceAdmissionDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
def sourceReserve {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):ℝ :=
  max (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
    min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
    Real.logb Z fixedPresentationCost-Real.logb Z cost+
    Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
    (Fintype.card α:ℝ)*Real.logb Z (max 1 childInput.upper)) 0

lemma sourceReserve_nonneg {α:Type*}[Fintype α] (s:Input ι)(childInput:Input α)
    (C D:Ideal O)(Z delta reserve cost a:ℝ):0≤sourceReserve s childInput C D Z delta reserve cost a :=
  le_max_right _ _

lemma common_affine (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)
    (Z κ A M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hp:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M):
    A+(6*κ-1)*(∑i:liveIndices B.val,Real.logb Z (s.P i.val))≤M := by
  have hs:=common_slot_logs_le s C B Z hZ hP
  have hm:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_admission (s:Input ι)(τ υ:AngularCharacter)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:CompletedGauss.primeSupport C₂=CompletedGauss.primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (child s C R0 B τ t).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (child s C R0 B τ t).ν (child s C R0 B τ t).W (child s C R0 B τ t).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=child s C R0 B τ t;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*(sigma/3)+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ):=mul_pos hcost hq
  have hf:=inherited_affine_parent s C R0 B Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(child s C R0 B τ t).P i:=fun i=>hP i.val
  have hparent:=common_affine (child s C R0 B τ t) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (child s C R0 B τ t) υ t) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ))-
      Real.logb Z (volume (child s C R0 B τ t))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (child s C R0 B τ t) υ t S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)) n hqref hrad ha hZ hlower hne
  rw [common_volume,Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices B.val):ℝ)*Real.logb Z (max 1 (child s C R0 B τ t).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.sourceReserve_nonneg
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.sourceReserve_nonneg

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_affine
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_affine

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_main_admission
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_main_admission
