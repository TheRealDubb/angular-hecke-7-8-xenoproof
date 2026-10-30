import AngularPhysicalPlainCanonicalFirst

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstColumns
open CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentSourceRow (primary_span_supported)
local notation "O" => ActualEisensteinCubic.O


open CenteredMomentSupportedCorrelation

theorem rowWeight_one_primary (η : AngularCharacter) (m : O) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    rowWeight η m 1 1 t I=η.elementCoeff (CompletedGauss.primaryGenerator I)*
      coprimalityMask m (CompletedGauss.primaryGenerator I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have he : η.idealHom I=η.elementCoeff (CompletedGauss.primaryGenerator I) := by
    have hh := η.idealHom_span (CompletedGauss.primaryGenerator I)
    rw [hs] at hh
    exact hh
  have hm : idealRowHom (m^6) I=coprimalityMask m (CompletedGauss.primaryGenerator I) := by
    have hh := idealRowHom_sixth_eq_mask m _ (hs.symm ▸ hI)
    rw [hs] at hh
    exact hh
  change (η.idealHom I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
  rw [mul_one,mul_one,he,hm]

theorem ideal_height_of_primary (η τ : AngularCharacter) (m : O) (F : O → ℂ)
    (hτ : ∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
      τ.elementCoeff n=η.elementCoeff n*coprimalityMask m n*F n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    τ.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
      rowWeight η m 1 1 t I*F (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  have he := hτ (CompletedGauss.primaryGenerator I) (hs.1.symm ▸ hI) hs.2
  rw [← τ.idealHom_span (CompletedGauss.primaryGenerator I),hs.1] at he
  rw [he,rowWeight_one_primary η m t I hI]
  ring

theorem exists_first_ideal_pair (η : AngularCharacter) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : AngularCharacter,τ₁.k=η.k ∧ τ₂.k=η.k ∧ τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        τ₁.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (leftCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₁ (CompletedGauss.primaryGenerator I))) ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        τ₂.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (rightCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₂ (CompletedGauss.primaryGenerator I))) := by
  obtain ⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,h₁,h₂⟩ := exists_canonical_first_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,?_,?_⟩
  · intro I hI t
    apply ideal_height_of_primary η τ₁ m
      (fun n => leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₁ n) _ I hI t
    intro n hn hp
    rw [h₁ n hn hp]
    ring
  · intro I hI t
    apply ideal_height_of_primary η τ₂ m
      (fun n => rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₂ n) _ I hI t
    intro n hn hp
    rw [h₂ n hn hp]
    ring

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.exists_first_ideal_pair
