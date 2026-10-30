import AngularPhysicalMainSourceAdmission

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
local instance angularErrorSourceAdmissionDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _
theorem actual_active_error_admission (s:Input ι)(τ υ:AngularCharacter)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:CompletedGauss.primeSupport C₂=CompletedGauss.primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).ν (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).W (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤Mdecl):
    let input:=errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+6*errorRemoval p Z k+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k):=by positivity
  have hf:=active_error_parent_affine s C R0 B τ t (Ideal.span {p}) k Bp υ v Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P i:=fun i=>hP i.val.val
  have hparent:=common_affine (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

theorem actual_width_admission {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayFourExpansion.RayCharacter→AngularCharacter}
    (hf:SecondFamily.Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (qref Z:ℝ)(hq:(η.modulus.absNorm:ℝ)≤qref)(hZ:1<Z)(χ:RayFourExpansion.RayCharacter):
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)-
      Real.logb Z (envelopeRef qref C D U n)≤0 := by
  have hh:=actual_width_le_reference hf t S β R rows W K hK n hne qref Z hq hZ χ
  linarith

lemma common_preVolume_height (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ υ:AngularCharacter)(v t:ℝ):
    preVolume (commonData (withHeight s τ v) C R B)=
      preVolume (commonData (withHeight s υ t) C R B) := rfl

end OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_active_error_admission
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_active_error_admission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_width_admission
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.actual_width_admission

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_preVolume_height
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstSourceAdmission.common_preVolume_height
