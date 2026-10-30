import AngularPhysicalSecondRadicalFamily

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
theorem child_modulus_bound (η : AngularCharacter) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm≤η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  have hn : η.modulus*Ideal.span {(12:O)}≠0 := mul_ne_zero η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  have hd : (childCharacter η χ).modulus∣η.modulus*Ideal.span {(12:O)} := by
    apply Ideal.dvd_iff_le.mpr
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) (map_dvd Ideal.absNorm hd)

theorem exists_second_budgeted_family (η : AngularCharacter) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : AngularCharacter, τ.k=η.k ∧
      (∀n:O,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*
        (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  obtain ⟨τ,hk,hN,he,ht⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,hk,he,ht,?_⟩
  intro hD hCD w hne
  have h1 := child_modulus_bound η χ
  have h2 := active_radical_norm_bound C D hC hD hCD U w hne
  apply hN.trans
  calc
    _≤(η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)) h2
    _=_ := by unfold fixedFactor;ring

theorem conductor_log_bound (η τ : AngularCharacter) (A B : Ideal O) (hA : A≠0) (hB : B≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*A.absNorm*B.absNorm)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z (A.absNorm:ℝ)+Real.logb Z (B.absNorm:ℝ) := by
  have hτ : (0:ℝ)<τ.modulus.absNorm := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  have hη : (η.modulus.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hK : (fixedFactor:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt fixedFactor_pos)
  have ha : (A.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  have hb : (B.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hh := Real.logb_le_logb_of_le hZ hτ (show (τ.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*fixedFactor*A.absNorm*B.absNorm by exact_mod_cast hN)
  rwa [Real.logb_mul (mul_ne_zero (mul_ne_zero hη hK) ha) hb,
    Real.logb_mul (mul_ne_zero hη hK) ha,Real.logb_mul hη hK] at hh

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.exists_second_budgeted_family
#print axioms OAI.SevenEighths.Angular.SecondFamily.conductor_log_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.conductor_log_bound
