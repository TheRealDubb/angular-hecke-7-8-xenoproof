import AngularPhysicalSecondConductorBudget
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth

noncomputable section
open scoped Classical BigOperators Topology
namespace OAI.SevenEighths.Angular.SecondFamily
open PlainRows ChildRows AngularRowClosure
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalLedger
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentCanonicalFirst CenteredMomentPartitionNorm CenteredMomentSupport
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentSecondRadicalFamily (active_radical_product)
open CenteredMomentSecondRadicalBudget (fixedFactor fixedFactor_pos active_radical_norm_bound)
local notation "O" => ActualEisensteinCubic.O
open CenteredMomentSecondRetainedWidth (retained_geometry)
open CenteredMomentSectorLocalization
theorem retained_log_budget (η τ : AngularCharacter) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (max 1 (4*R/(normValue G*normValue V)))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨hR,hG,hV,_,_,_,hmax⟩:=retained_geometry R G V z hne
  have hg:=normValue_pos G hG
  have hv:=normValue_pos V hV
  have hF : (fixedFactor:ℝ)≠0:=by exact_mod_cast fixedFactor_pos.ne'
  have hc:=conductor_log_bound η τ U (Ideal.span {V}) hU
    (Ideal.span_singleton_eq_bot.not.mpr hV) hN Z hZ
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z (U.absNorm:ℝ)+Real.logb Z (normValue V) at hc
  rw [max_eq_right hmax,Real.logb_div (mul_ne_zero (by norm_num) hR.ne')
    (mul_ne_zero hg.ne' hv.ne'),Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne',
    Real.logb_mul hg.ne' hv.ne',Real.logb_mul (by norm_num : (4:ℝ)≠0) hF]
  linarith

theorem retained_row_log_budget (η τ : AngularCharacter) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨_,_,_,hz,_,hn,_⟩:=retained_geometry R G V z hne
  have hh:=Real.logb_le_logb_of_le hZ (normValue_pos z hz) (hn.trans (le_max_right 1 _))
  have hb:=retained_log_budget η τ G V z U hU hN R Z hZ hne
  linarith

theorem exists_retained_width_family (η : AngularCharacter) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : AngularCharacter, τ.k=η.k ∧
      (∀n:O,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,1<Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨τ,hk,he,ht,hN⟩:=exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,hk,he,ht,?_⟩
  intro hD hCD w hw
  have hb:=hN hD hCD w hw
  refine ⟨hb,?_⟩
  intro Z R hZ z hz
  have hU : (∏P∈U,P.val)≠0:=Finset.prod_ne_zero_iff.mpr
    (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  obtain ⟨hR,_,_,hne,h1,hrow,_⟩:=retained_geometry R _ _ z hz
  exact ⟨hR,hne,h1,hrow,retained_log_budget η τ _ _ z _ hU hb R Z hZ hz,
    retained_row_log_budget η τ _ _ z _ hU hb R Z hZ hz⟩

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.exists_retained_width_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.exists_retained_width_family
