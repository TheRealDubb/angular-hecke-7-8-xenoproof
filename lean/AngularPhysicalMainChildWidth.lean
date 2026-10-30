import AngularPhysicalAmplifiedMainWidth
import AngularPhysicalCanonicalMainPaid
import OAI.NumberTheory.DirichletL.Energy.AmplifiedChildWidth
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.CanonicalChildWidth
open ActualEisensteinCubic ConcretePrimeRowBridge PlainRows CommonRows
open PlainRows.ChildInputs PlainRows.ChildSourceCaps PlainRows.FirstAnnularInput
open PlainRows.FirstSourceAdmission PhysicalBlock SecondFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonical
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open CenteredMomentFirstCanonicalFamily (subsetGenerator_supported)
open CenteredMomentSecondDyadicRowSupport (dyadicRows_norm)
open CenteredMomentAmplificationChildSourceCaps (norm_ge_one)
open CenteredMomentEnergyAmplifiedChildWidth
  (geometry geometry_pos mainRadius mainRadius_eq threshold threshold_gt_one ball_support)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance {α:Type*}:DecidableEq α:=Classical.decEq _
theorem actual_ball_witness (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z≠0 ∧ ballProfile (normValue z/dyadicScale (n 1))=1 := by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  refine ⟨z,hz0,ballProfile_one _ (div_nonneg (normValue_pos z hz0).le (dyadicScale_pos _).le) ?_⟩
  exact (div_le_one (dyadicScale_pos _)).mpr (dyadicRows_norm rows n z hz).2.le

lemma main_nominal_cap (N:ℕ)(b:ℝ)(hb:1≤b)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C R:Ideal O)(B:actualAllocations s.pools C)
    (τ:AngularCharacter)(t K:ℝ)(hK:0<K)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    nominal (child s C R B τ t) K≤geometry N b*((volume s/(C.absNorm:ℝ))^2/K) := by
  have hv:=common_volume_le N b hb s hc hs C R B τ t hne
  have hC:=CenteredMomentAmplificationChildSourceCaps.norm_ge_one C (allocation_ne s C B)
  have hh:0≤volume s/(C.absNorm:ℝ):=div_nonneg (volume_pos s).le (by positivity)
  have hv':volume (child s C R B τ t)≤b^N*(volume s/(C.absNorm:ℝ)):=by simpa only [mul_div_assoc] using hv
  have hp:volume (child s C R B τ t)^2≤(b^N)^2*(volume s/(C.absNorm:ℝ))^2:=by
    nlinarith [volume_pos (child s C R B τ t),mul_nonneg (pow_nonneg (zero_le_one.trans hb) N) hh]
  exact (div_le_div_of_nonneg_right hp hK.le).trans_eq (by unfold geometry;ring)

theorem main_child_width (N:ℕ)(b σ:ℝ)(hb:1≤b)(hσ:0<σ)
    (Z:ℝ)(hlarge:threshold N b σ hb hσ≤Z)(s:Input ι)
    (hc:Fintype.card ι≤N)(hs:s.upper≤b)(C D R:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(τ:AngularCharacter)(t:ℝ)
    (hB:frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (K δ reserve ξ q Mparent:ℝ)(hK:0<K)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hη:(s.η.modulus.absNorm:ℝ)≤Z^q)(hparent:Real.logb Z K+q≤Mparent)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)(hC₂:Supported C₂)(hD₂:Supported D₂)
    (U:Finset (CommonIndex C₂ D₂))(family:RayCharacter→AngularCharacter)
    (hf:Family τ C₂ D₂ hC₂ hD₂ U family)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hne:physicalBlock τ t S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (nominal (child s C R B τ t) (mainRadius C D E K (volume s) Z σ δ reserve)) Z ξ)
      rows W (mainRadius C D E K (volume s) Z σ δ reserve) n≠0)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)<Mparent-σ/2 := by
  have hZ:1<Z:=(threshold_gt_one N b σ hb hσ).trans_le hlarge
  let L:=mainRadius C D E K (volume s) Z σ δ reserve
  have hL:0<L:=by unfold L mainRadius mainCommonRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have he:=mainRadius_eq C D hC hD hCD E K (volume s) Z σ δ reserve
  have hscale:=main_nominal_cap N b hb s hc hs C R B τ t L hL hB
  have hhscale:nominal (child s C R B τ t) L≤geometry N b*
      ((volume s/((commonPart C D).absNorm:ℝ))^2/L):=by
    simpa only [commonPart_eq_left C D hC.1 hCD] using hscale
  obtain ⟨z,hz,hball⟩:=actual_ball_witness τ t S β C₂ D₂ hC₂ hD₂ U _ rows W L n hne
  have hw:=main_declared_width_drop s.η τ fixedBadMask fixedBadMask_ne_zero C D E
    K (volume s) Z σ δ reserve hK (volume_pos s) hZ hmod hf t S β rows W
    (nominal (child s C R B τ t) L) (geometry N b) ξ (nominal_pos _ L hL)
    (geometry_pos N b hb) (by simpa only [←he] using hhscale) n
    (by simpa only [←he] using hne) χ ballProfile 2 (by norm_num) ball_support z hz
    (by rw [hball];exact one_ne_zero) rfl q hη hσ hδ hr hξ hlarge
  have hlog:Real.logb Z (dyadicScale (n 1))≤Real.logb Z (max 1 (2*dyadicScale (n 1))):=by
    apply Real.logb_le_logb_of_le hZ (dyadicScale_pos _)
    exact (by linarith [dyadicScale_pos (n 1)]:dyadicScale (n 1)≤2*dyadicScale (n 1)).trans (le_max_right _ _)
  linarith


end OAI.SevenEighths.Angular.CanonicalChildWidth

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.actual_ball_witness
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.actual_ball_witness

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.main_nominal_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.main_nominal_cap

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.main_child_width
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.main_child_width
