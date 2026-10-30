import AngularPhysicalPlainSecondFamily
import OAI.NumberTheory.DirichletL.Moments.AmplificationOriginalErrors

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.Amplification
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
local instance angularAmplificationFamilyDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

theorem exists_amplification_family (η : AngularCharacter) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → AngularCharacter,
      (∀ χ,(τ χ).k=η.k) ∧
      (∀ χ, (τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I := by
  choose τ hk hN hτ using fun χ : RayCharacter =>
    exists_second_height_character η χ m (p^(2*k)) hm (pow_ne_zero _ hp) hmLam hm2
  refine ⟨τ,hk,hN,?_⟩
  intro I hI t
  have hn := supported_primaryGenerator_ne_zero I hI
  have hgen : Supported (Ideal.span {primaryGenerator I}) := by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem original_column_family (η : AngularCharacter) (m p : O) (k : ℕ)
    (τ : RayCharacter → AngularCharacter)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro χ hχ;ring


end OAI.SevenEighths.Angular.PlainRows.Amplification

#print axioms OAI.SevenEighths.Angular.PlainRows.Amplification.exists_amplification_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.Amplification.exists_amplification_family
