import AngularPhysicalPlainSecondFamily

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainRows
open ChildRows ExceptionalRows
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
open CenteredMomentSourceRow (primary_span_supported)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero fixedBadMask_coprime)
local notation "O" => ActualEisensteinCubic.O

theorem row_presentation_height (η τ : AngularCharacter) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 A n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  have he := InverseRows.idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1 A hτ I
  have he' : heightCoeff τ t I=rowWeight (childCharacter η χ) fixedBadMask 1 A t I := by
    change τ.idealHom I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [he]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_pow,one_mul,mul_one]
  rw [he',rowWeight_split,←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI]
  simp only [heightCoeff,child_ideal_primary η χ I hI]
  ring

theorem exists_second_family_presentation (η : AngularCharacter) (χ : RayCharacter)
    (A : O) (hA : A≠0) :
    ∃ τ : AngularCharacter, τ.k=η.k ∧
      τ.modulus.absNorm≤AngularRowClosure.rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      (∀ n,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 A n) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hk,hN,hτ,_⟩ := AngularRowClosure.exists_angular_row_character
    (childCharacter η χ) fixedBadMask 1 A
    fixedBadMask_ne_zero one_ne_zero hA (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨τ,hk,hN,hτ,fun I hI t => row_presentation_height η τ χ A hτ I hI t⟩

theorem row_presentation_twist (η τ : AngularCharacter) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 A n)
    (z n : O) :
    rowTwist τ.elementHom.toMonoidHom fixedBadMask 1 z n=
      rowTwist (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [ite_eq_left (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change τ.elementCoeff n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : ConcretePrimeRowBridge.goodLambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported τ.elementHom.toMonoidHom fixedBadMask 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 (A*z) n hmLam hm2 hn).symm

theorem fixedInducingRow_transport (η τ : AngularCharacter) (htype : τ.k=η.k) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [htype,childCharacter_k,one_mul,row_presentation_twist η τ χ A hτ]

theorem nonexceptional_transport (η τ : AngularCharacter) (htype : τ.k=η.k) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,τ.elementCoeff n=rowTwist (childCharacter η χ).elementHom.toMonoidHom fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    nonexceptional η χ Q fixedBadMask A z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [nonexceptional,fixedInducingRow_transport η τ htype χ A hτ Q z]

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.nonexceptional_transport
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.nonexceptional_transport
