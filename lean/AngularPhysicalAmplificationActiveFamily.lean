import AngularPhysicalAmplificationFamilyEnergy

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
local instance angularAmplificationActiveFamilyDecEq {κ:Type*} : DecidableEq κ := Classical.decEq _

theorem exists_actual_error_family (η : AngularCharacter) (m p : O)
    (hm : m≠0) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → AngularCharacter,
      (∀ χ,(τ χ).k=η.k) ∧
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1
        (p^(2*errorMovingExponent n))) ∧
      ∀ (S : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hk,hN,hτ⟩ := exists_amplification_energy_family η m p hm hp.ne_zero hs hpp hmLam hm2
    (errorMovingExponent n)
  refine ⟨τ,hk,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact hτ (residualColumns S p hp (n+1)) C hC β t W K hK hW


end OAI.SevenEighths.Angular.PlainRows.Amplification

#print axioms OAI.SevenEighths.Angular.PlainRows.Amplification.exists_actual_error_family
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.Amplification.exists_actual_error_family
