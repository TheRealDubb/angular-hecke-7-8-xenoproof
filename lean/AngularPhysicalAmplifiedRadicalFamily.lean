import AngularPhysicalRadicalPresentation
import AngularPhysicalAmplificationFamilyEnergy
import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalFamily
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AmplifiedRadical
open AngularRowClosure ChildRows CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationErrorPool CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationChildEnergy CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationFamily
  (amplificationPhase amplificationPhase_expansion amplificationPhase_norm)
open CenteredMomentAmplificationActiveFamily (actual_error_energy_active)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [instι:Fintype ι]
local instance successorRadicalDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

open PlainRows PlainRows.Amplification
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
def radicalBound (η:AngularCharacter)(m p:O)(k:ℕ):ℕ :=
  η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (if k=0 then 1 else (Ideal.span {p}).absNorm)

theorem radicalBound_error_power (η:AngularCharacter)(m p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    (radicalBound η m p (errorMovingExponent n):ℝ)=
      ((η.modulus.absNorm:ℝ)*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm)*
        Z^(errorMoving p Z (n+1)):=by
  have hpow:=Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)
  rcases hn with rfl|rfl|rfl <;>
    norm_num only [radicalBound,errorMovingExponent,errorMoving,Nat.cast_mul,
      Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals simp only [ite_false,ite_true,Nat.one_ne_zero,eq_self,
    Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals rw [hpow]; rfl

theorem exists_radical_row (η:AngularCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:AngularCharacter,τ.k=η.k ∧ τ.modulus.absNorm≤radicalBound η m p k ∧
      ∀n:O,τ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (p^(2*k)) n:=by
  by_cases hk:k=0
  · obtain ⟨τ,hkType,hN,hτ⟩:=exists_supported_row_presentation η m 1 hm
      CenteredMomentAddedZero.supported_one_element hmLam hm2
    refine ⟨τ,hkType,?_,?_⟩
    · simp [radicalBound,hk,hN]
    · simpa [hk] using hτ
  · obtain ⟨τ,hkType,hM,hN,hτ⟩:=exists_radical_row_presentation η m hm hmLam hm2
      (fun _:Fin 1=>p) (fun _=>hs) (fun _=>2*k)
      (fun _=>Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk))
    refine ⟨τ,hkType,?_,?_⟩
    · simpa [radicalBound,hk] using hN
    · simpa using hτ

theorem exists_radical_height (η:AngularCharacter)(χ:RayCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:AngularCharacter,τ.k=η.k ∧ τ.modulus.absNorm≤radicalBound (childCharacter η χ) m p k ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom (p^(2*k)) I*
          rayCharacter χ (primaryGenerator I):=by
  obtain ⟨τ,hkType,hN,hτ⟩:=exists_radical_row (childCharacter η χ) m p hm hs hmLam hm2 k
  refine ⟨τ,hkType,hN,?_⟩
  intro I hI t
  have he:=InverseRows.idealCoeff_eq_row (childCharacter η χ) τ m 1 (p^(2*k)) hτ I
  simp only [one_pow,mul_one] at he
  change τ.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((η.idealHom I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom (p^(2*k)) I*rayCharacter χ (primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem exists_radical_family (η:AngularCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hpp:goodLambda^2∣p-1)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:RayCharacter→AngularCharacter,
      (∀χ,(τ χ).k=η.k) ∧
      (∀χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p k) ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑χ:RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I:=by
  choose τ hkType hN hτ using fun χ:RayCharacter=>exists_radical_height η χ m p hm hs hmLam hm2 k
  refine ⟨τ,hkType,hN,?_⟩
  intro I hI t
  have hn:=supported_primaryGenerator_ne_zero I hI
  have hgen:Supported (Ideal.span {primaryGenerator I}):=by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem exists_actual_error_family (η:AngularCharacter)(m p:O)
    (hm:m≠0)(hp:Prime p)(hs:Supported (Ideal.span {p}))
    (hpp:goodLambda^2∣p-1)(hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    ∃τ:RayCharacter→AngularCharacter,
      (∀χ,(τ χ).k=η.k) ∧
      (∀χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀(S:Finset (Ideal O))(C:Ideal O),C≠0→∀(β:Ideal O→ℂ)(t:ℝ)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I=>β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I=>residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑χ:RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I=>β (C*I)) (heightCoeff (τ χ) t) W K).re:=by
  obtain ⟨τ,hkType,hN,hτ⟩:=exists_radical_family η m p hm hs hpp hmLam hm2 (errorMovingExponent n)
  refine ⟨τ,hkType,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact amplification_family_energy η m p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) C hC β t W K hK hW


end OAI.SevenEighths.Angular.AmplifiedRadical

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.radicalBound_error_power
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.radicalBound_error_power

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.exists_radical_row
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.exists_radical_row

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.exists_radical_height
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.exists_radical_height

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.exists_radical_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.exists_radical_family

#print axioms OAI.SevenEighths.Angular.AmplifiedRadical.exists_actual_error_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AmplifiedRadical.exists_actual_error_family
