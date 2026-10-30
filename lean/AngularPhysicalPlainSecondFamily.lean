import AngularPhysicalPlainReflected
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open ChildRows ExceptionalRows
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
open CenteredMomentSourceRow (primary_span_supported)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero fixedBadMask_coprime)
local notation "O" => ActualEisensteinCubic.O


open CenteredMomentChildAssembly CenteredMomentSecondScaled

theorem child_ideal_primary (η : AngularCharacter) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    (childCharacter η χ).idealHom I=η.idealHom I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := (childCharacter η χ).idealHom_span (CompletedGauss.primaryGenerator I)
  have he := η.idealHom_span (CompletedGauss.primaryGenerator I)
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

theorem exists_second_height_character (η : AngularCharacter) (χ : RayCharacter) (m A : O)
    (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : AngularCharacter,τ.k=η.k ∧ τ.modulus.absNorm≤AngularRowClosure.rowConductorBound (childCharacter η χ) m 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
          rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  obtain ⟨τ,hk,hN,hτ,_⟩ := AngularRowClosure.exists_angular_row_character
    (childCharacter η χ) m 1 A hm one_ne_zero hA hmLam hm2
  refine ⟨τ,hk,hN,?_⟩
  intro I hI t
  have he := InverseRows.idealCoeff_eq_row (childCharacter η χ) τ m 1 A hτ I
  simp only [one_pow,mul_one] at he
  change τ.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((η.idealHom I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem second_divisor_column (η τ : AngularCharacter) (χ : RayCharacter) (m A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => CompletedGauss.primaryGenerator J)
        (fun J => β J*rowWeight η m 1 1 t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

theorem heightCoeff_eq_fixed_rowWeight (τ : AngularCharacter) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [ite_eq_left hc.symm] at hs
  change τ.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((τ.idealHom I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.exists_second_height_character
