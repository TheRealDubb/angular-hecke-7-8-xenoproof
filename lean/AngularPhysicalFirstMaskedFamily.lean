import AngularPhysicalPlainFirstIdeal
import AngularPhysicalPlainSecondFamily
import AngularPhysicalPlainReflected
import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstMaskedFamily (idealMask maskedSource idealMask_primary fixed_mask_ne_zero sourceGaussEnergy_congr)
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentSourceRow CenteredMomentFirstCanonicalFamily CenteredMomentPrimitive
open CenteredMomentSourceAllocationEnergy
open ActualEisensteinCubic CenteredMomentChildAssembly CenteredMomentOriginalChildEnergy
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O

lemma row_mask_factor (η : AngularCharacter) (u z n : O) :
    rowTwist η.elementHom.toMonoidHom (fixedBadMask*u) 1 z n =
      (if IsCoprime n u then (1:ℂ) else 0)*
        rowTwist η.elementHom.toMonoidHom fixedBadMask 1 z n := by
  have h := ExceptionalRows.row_mask_mul η fixedBadMask u 1 z n
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda)
  simp only [one_mul] at h
  rw [h]
  split_ifs <;> simp

lemma rowWeight_mask_factor (η : AngularCharacter) (u : O) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change η.elementCoeff (primaryGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryGenerator I) u then (1:ℂ) else 0) *
      (η.elementCoeff (primaryGenerator I) *
        (if IsCoprime fixedBadMask (primaryGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryGenerator I)
  <;> by_cases hu : IsCoprime (primaryGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryGenerator I) ↔
      IsCoprime (primaryGenerator I) u from isCoprime_comm]

theorem exists_canonical_masked_pair (η : AngularCharacter) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : AngularCharacter, τ₁.k=η.k ∧ τ₂.k=η.k ∧ τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hk₁,hk₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

lemma divisor_column_masked (η τ : AngularCharacter) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (u : O) (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma first_source_energy (η τ : AngularCharacter) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy Q β
      (fun I => rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I)) W K =
    sourceGaussEnergy Q (maskedSource u β) (heightCoeff τ t) W K := by
  apply sourceGaussEnergy_congr
  intro I _ hI
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  simp only [maskedSource]
  ring

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.row_mask_factor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.row_mask_factor

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.rowWeight_mask_factor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.rowWeight_mask_factor

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.exists_canonical_masked_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.exists_canonical_masked_pair

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.divisor_column_masked
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.divisor_column_masked

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.first_source_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.first_source_energy
