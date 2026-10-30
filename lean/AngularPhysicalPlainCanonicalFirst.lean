import AngularPhysicalPlainFirstCharacter
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstColumns
open CenteredMomentPrimitive CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentSourceRow (primary_span_supported)
local notation "O" => ActualEisensteinCubic.O


open CenteredMomentFirstCanonicalFamily (subsetGenerator_supported activeConductor_supported
  canonicalActiveCharacter canonicalActiveCharacter_mk)

theorem exists_canonical_first_pair (η : AngularCharacter) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (I J : Ideal O) (hI : Supported I) (E : Finset (CommonIndex I J))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let r := activeConductor I J
    let ρ := finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : AngularCharacter,τ₁.k=η.k ∧ τ₂.k=η.k ∧ τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        τ₁.elementCoeff n=η.elementCoeff n*coprimalityMask m n*leftCoefficient e r ρ n*rayCharacter ξ₁ n) ∧
      (∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
        τ₂.elementCoeff n=η.elementCoeff n*coprimalityMask m n*rightCoefficient e r ρ n*rayCharacter ξ₂ n) := by
  dsimp only
  obtain ⟨τ₁,hk₁,hM₁,_,h₁⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI) ξ₁
  obtain ⟨τ₂,hk₂,hM₂,_,h₂⟩ := exists_first_character η m
    (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) (activeConductor I J) hm
    (subsetGenerator_supported I J hI E) (activeConductor_supported I J hI) hmLam hm2
    (canonicalActiveCharacter I J hI)⁻¹ ξ₂
  refine ⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,?_,?_⟩
  · intro n hn hp
    rw [h₁ n hn hp,canonicalActiveCharacter_mk,leftCoefficient]
    ring
  · intro n hn hp
    let : Finite (Residue (activeConductor I J)) := finite_quotient_span (finitePrimeModulus_ne_zero (activePrime I J))
    rw [h₂ n hn hp,← MulChar.star_apply',canonicalActiveCharacter_mk,rightCoefficient]
    ring

theorem first_displayed_norm (η : AngularCharacter) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) :
    (η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}).absNorm =
    η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏ P∈E,P.val).absNorm*(Ideal.span {activeConductor I J}).absNorm) := by
  rw [← Ideal.span_singleton_mul_span_singleton,primeSubsetGenerator,span_idealGenerator]
  simp only [map_mul]

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.exists_canonical_first_pair
