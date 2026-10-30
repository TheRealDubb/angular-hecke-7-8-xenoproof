import AngularPhysicalSecondChildWidth
import AngularPhysicalPlainCanonicalFirst
import OAI.NumberTheory.DirichletL.Moments.AmplifiedChildWidth
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
theorem modulus_pos (η:AngularCharacter) : 0<(η.modulus.absNorm:ℝ) :=
  norm_pos _ η.modulus_ne_bot
theorem canonical_modulus_log (η ρ:AngularCharacter)(m:O)(hm:m≠0)
    (I J:Ideal O)(A:Finset (CommonIndex I J))(Z:ℝ)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    Real.logb Z (ρ.modulus.absNorm:ℝ)=
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((∏P∈A,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
  have he:0<((∏P∈A,P.val).absNorm:ℝ) := by
    apply norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [hmod,PlainRows.first_displayed_norm]
  push_cast
  rw [Real.logb_mul (mul_pos (mul_pos (modulus_pos η) (span_pos m hm))
      (span_pos 72 (by norm_num))).ne' (mul_pos he (active_norm_pos I J)).ne',
    Real.logb_mul (mul_pos (modulus_pos η) (span_pos m hm)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (modulus_pos η).ne' (span_pos m hm).ne',
    Real.logb_mul he.ne' (active_norm_pos I J).ne']
  ring

theorem main_nominal_bound (η ρ:AngularCharacter)(m:O)(hm:m≠0)(I J:Ideal O)
    (A:Finset (CommonIndex I J))(K X Z σ δ reserve:ℝ)
    (hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    2*Real.logb Z (X/(commonPart I J).absNorm)-
      Real.logb Z (mainCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve)+
      Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)-
      2*σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [Real.logb_div hX.ne' (norm_pos _ (commonPart_ne_zero I J)).ne',
    mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    nominalLog,CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX,
    canonical_modulus_log η ρ m hm I J A Z hmod]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) (0:ℝ)]

theorem physical_radial_budget {η:AngularCharacter}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→AngularCharacter}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hw:=radial_radius_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W L hL n hne Z hZ χ b hb
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (div_pos (sq_pos_of_pos hH) hL).ne',
    Real.logb_div (sq_pos_of_pos hH).ne' hL.ne',Real.logb_pow] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      2*Real.logb Z H-Real.logb Z L+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    push_cast at hl
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : (16:ℝ)*b*fixedFactor≠0)]
    congr 1
    ring
  rw [hf]
  linarith

theorem physical_declared_budget {η:AngularCharacter}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→AngularCharacter}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  linarith

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

theorem main_nominal_fixed :
    2*Real.logb Z Hx-Real.logb Z Lm+Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-2*σ-δ-reserve := by
  have hh:=main_nominal_bound η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  linarith [first_fixed_log_le Z hZ]

theorem main_declared_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→AngularCharacter}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_declared_width_drop {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→AngularCharacter}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=main_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith


end ActualSource
end OAI.SevenEighths.Angular.CanonicalChildWidth

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.modulus_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.modulus_pos

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.canonical_modulus_log
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.canonical_modulus_log

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.main_nominal_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.main_nominal_bound

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.physical_radial_budget
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.physical_radial_budget

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.physical_declared_budget
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.physical_declared_budget

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.main_nominal_fixed
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.main_nominal_fixed

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.main_declared_width
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.main_declared_width

#print axioms OAI.SevenEighths.Angular.CanonicalChildWidth.main_declared_width_drop
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CanonicalChildWidth.main_declared_width_drop
