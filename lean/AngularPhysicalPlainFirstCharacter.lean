import AngularPhysicalFiniteProductPresentation

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PlainRows
open AngularRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimaryCharacter CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem first_period_contains (η : AngularCharacter) (m e r : O) :
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    M≤Ideal.span {3*r} ∧ M≤Ideal.span {(12:O)} := by
  dsimp only
  constructor
  · calc
      _ ≤ Ideal.span {(72:O)}*Ideal.span {e*r} := by
        rw [mul_assoc]
        exact Ideal.mul_le_right
      _ = Ideal.span {(72:O)*(e*r)} := Ideal.span_singleton_mul_span_singleton _ _
      _ ≤ _ := Ideal.span_singleton_le_span_singleton.mpr ⟨24*e,by ring⟩
  · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)

theorem exists_first_character (η : AngularCharacter) (m e r : O)
    (hm : m≠0) (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : AngularCharacter, τ.k=η.k ∧
      τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O,τ.elementCoeff n=
        rowTwist η.elementHom.toMonoidHom m 1 (e*r) n*maskedPrimaryHom r χ n*
          HeckeFamily.elementCoeff (primaryRayCharacter ξ) n) ∧
      ∀ n : O,Supported (Ideal.span {n}) → λ₀^2∣n-1 →
        τ.elementCoeff n=η.elementCoeff n*coprimalityMask m n*
          idealRowHom (e*r) (Ideal.span {n})*χ (Ideal.Quotient.mk _ n)*rayCharacter ξ n := by
  obtain ⟨τ₀,hk,hM,hτ⟩ := exists_supported_row_presentation η m (e*r) hm (supported_mul_elements e r he hr) hmLam hm2
  let τ := finiteTwist (finiteTwist τ₀ (primaryCharacter r (supported_element_ne_zero r hr) χ)) (primaryRayCharacter ξ)
  have hp := first_period_contains η m e r
  refine ⟨τ,hk,?_,?_,?_⟩
  · change (τ₀.modulus ⊓ (primaryCharacter r (supported_element_ne_zero r hr) χ).modulus) ⊓
      (primaryRayCharacter ξ).modulus=_
    rw [hM,primaryCharacter_modulus,primaryRayCharacter_modulus,inf_eq_left.mpr hp.1,inf_eq_left.mpr hp.2]
  · intro n
    rw [show τ=finiteTwist (finiteTwist τ₀ (primaryCharacter r (supported_element_ne_zero r hr) χ)) (primaryRayCharacter ξ) from rfl,
      elementCoeff_finiteTwist,elementCoeff_finiteTwist,hτ,primaryCharacter_all]
  · intro n hn hpn
    rw [show τ=finiteTwist (finiteTwist τ₀ (primaryCharacter r (supported_element_ne_zero r hr) χ)) (primaryRayCharacter ξ) from rfl,
      elementCoeff_finiteTwist,elementCoeff_finiteTwist,hτ,primaryCharacter_primary r _ χ n hpn,
      primaryRayCharacter_primary ξ n hn hpn,rowTwist_extract_sixth_mask _ m 1 (e*r) n hn]
    simp only [one_pow,one_mul]
    rfl

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.exists_first_character
