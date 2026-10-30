import AngularPhysicalAmplifiedMainWidth
import AngularPhysicalAmplifiedRadicalFamily
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.CanonicalChildWidth
open ActualEisensteinCubic PlainRows PhysicalBlock SecondFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization
open CenteredMomentSecondActualWidth (actual_common_log_ge_unit)
open CenteredMomentAmplifiedChildWidth
  (span_pos presentationFactor presentationFactor_pos first_fixed_log_le
    fixedWidthThreshold fixedWidthThreshold_spec)
local notation "O" => ActualEisensteinCubic.O
open AmplifiedRadical ChildRows
open CenteredMomentAmplificationActiveFactor (errorMovingExponent)
open CenteredMomentAmplifiedChildWidth (shortened_log presentationFactor_log)
theorem radical_error_log_bound (ρ η:AngularCharacter)(χ:RayCharacter)(m p:O)
    (hm:m≠0)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:η.modulus.absNorm≤radicalBound (childCharacter ρ χ) m p (errorMovingExponent n)) :
    Real.logb Z (η.modulus.absNorm:ℝ)≤
      Real.logb Z (ρ.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+errorMoving p Z (n+1) := by
  have hmpos:=span_pos m hm
  have h12:=span_pos 12 (by norm_num)
  have h72:=span_pos 72 (by norm_num)
  have hρ:=modulus_pos ρ
  have hray:( (childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound ρ χ
  have hb:(η.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)) := by
    have hh:(η.modulus.absNorm:ℝ)≤(radicalBound (childCharacter ρ χ) m p (errorMovingExponent n):ℝ):=by exact_mod_cast hN
    rw [radicalBound_error_power _ m p hp Z hZ n hn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hray (by positivity))
        (by positivity)) (by positivity))
  have hh:=Real.logb_le_logb_of_le hZ (modulus_pos η) hb
  rw [Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm).ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*(Ideal.span {m}).absNorm).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (mul_pos (modulus_pos ρ) (span_pos 12 (by norm_num))).ne' (span_pos m hm).ne',
    Real.logb_mul (modulus_pos ρ).ne' (span_pos 12 (by norm_num)).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  linarith

theorem error_nominal_bound (η ρ θ:AngularCharacter)(χ:RayCharacter)(m₀ m₁ p:O)
    (hm₀:m₀≠0)(hm₁:m₁≠0)(hp:p≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
    (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m₀}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) m₁ p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m₀}).absNorm:ℝ)+Real.logb Z ((Ideal.span {m₁}).absNorm:ℝ)+
      2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)-σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  have hq:=radical_error_log_bound ρ θ χ m₁ p hm₁ hp Z hZ n hn hN
  rw [canonical_modulus_log η ρ m₀ hm₀ I J A Z hmod] at hq
  rw [shortened_log I J X Z hX p hp (n+1),errorCommonRadius,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',nominalLog,
    CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-2*errorRemoval p Z (n+1)+errorMoving p Z (n+1)) (0:ℝ)]

section ActualSource
variable (η ρ:AngularCharacter)(m:O)(hm:m≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
  (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
  (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})

local notation "cc" => Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)
local notation "dd" => Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)
local notation "kk" => nominalLog I J (∏P∈A,Subtype.val P) K X Z
local notation "Lm" => mainCommonRadius Z dd kk cc σ δ reserve
local notation "Hx" => X/Ideal.absNorm (commonPart I J)
local notation "parentWidth" => Real.logb Z K+Real.logb Z (Ideal.absNorm (AngularCharacter.modulus η):ℝ)+Real.logb Z (Ideal.absNorm (Ideal.span (Singleton.singleton m)):ℝ)
include σ δ reserve hm hK hX hZ hmod

theorem error_nominal_fixed (θ:AngularCharacter)(χ:RayCharacter)(p:O)(hp:p≠0)
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z dd kk cc σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-σ-δ-reserve := by
  have hh:=error_nominal_bound η ρ θ χ m fixedBadMask p hm fixedBadMask_ne_zero hp
    I J A K X Z σ δ reserve hK hX hZ hmod n hn hN
  rw [presentationFactor_log]
  linarith

theorem error_declared_width (θ:AngularCharacter)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→AngularCharacter}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_declared_width_drop (θ:AngularCharacter)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→AngularCharacter}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=error_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith


end ActualSource
end OAI.SevenEighths.Angular.CanonicalChildWidth

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.radical_error_log_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.radical_error_log_bound

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.error_nominal_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.error_nominal_bound

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.error_nominal_fixed
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.error_nominal_fixed

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.error_declared_width
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.error_declared_width

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.error_declared_width_drop
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.error_declared_width_drop
