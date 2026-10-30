import AngularPhysicalRayNonprincipal
import OAI.NumberTheory.DirichletL.Moments.ExceptionalPair

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open AngularRowClosure CanonicalRowCompletion ChildRows
open PrimaryVolume (InducedBy exists_primitive_inducedBy)
open RayFourExpansion CenteredMomentFixedRay
open CenteredMomentExceptionalPair (rayRatio reflectionRatio reflectionRatio_modulus)
local notation "O" => ActualEisensteinCubic.O

theorem finiteTwist_idealHom (χ : AngularCharacter) (τ : HeckeFamily.Character) (I : Ideal O) :
    (finiteTwist χ τ).idealHom I=χ.idealHom I*HeckeFamily.idealCoeff τ I := by
  by_cases hI : I=0
  · simp only [hI,map_zero,zero_mul]
  · rw [←ConcretePrimeRowBridge.span_idealGenerator I,AngularCharacter.idealHom_span,
      elementCoeff_finiteTwist,AngularCharacter.idealHom_span,
      HeckeFamily.idealCoeff_span τ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI)]

theorem fixed_primitive_finite_product (χ ψ : AngularCharacter) (htype : ψ.k=χ.k)
    (τ : HeckeFamily.Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hψ : Q≤ψ.modulus) (hτ : Q≤τ.modulus) :
    ∃ ρ : AngularCharacter, ρ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      Q≤ρ.modulus ∧ InducedBy (finiteTwist χ τ) ρ := by
  obtain ⟨ρ,hρk,hprim,hmod,hmask⟩ := exists_primitive_inducedBy (finiteTwist ψ τ)
  refine ⟨ρ,hρk.trans htype,hprim,(le_inf hψ hτ).trans hmod,?_⟩
  intro I
  by_cases hI : I=0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I (finiteTwist χ τ).modulus
  · have hn := (idealHom_ne_zero_iff (finiteTwist χ τ) I).mpr ⟨hI,hc⟩
    rw [finiteTwist_idealHom] at hn
    have hχ := (idealHom_ne_zero_iff χ I).mp (left_ne_zero_of_mul hn) |>.2
    have he : χ.idealHom I=ψ.idealHom I := by rw [h I,ite_eq_left hχ]
    have hnψ : (finiteTwist ψ τ).idealHom I≠0 := by
      rw [finiteTwist_idealHom,←he]
      exact hn
    have hcψ := (idealHom_ne_zero_iff (finiteTwist ψ τ) I).mp hnψ |>.2
    rw [ite_eq_left hc,finiteTwist_idealHom,he,←finiteTwist_idealHom,
      hmask I,ite_eq_left hcψ]
  · have hz : (finiteTwist χ τ).idealHom I=0 := by
      by_contra hn
      exact hc ((idealHom_ne_zero_iff (finiteTwist χ τ) I).mp hn).2
    rw [hz,ite_eq_right hc]

theorem fixedInducingRow_of_finite_product (η₁ η₂ : AngularCharacter) (htype : η₂.k=η₁.k)
    (τ : HeckeFamily.Character) (Q : Ideal O) (m A z₁ z₂ : O) (hτ : Q≤τ.modulus)
    (he : ∀ n, rowTwist η₂.elementHom.toMonoidHom m 1 (A*z₂) n=
      rowTwist η₁.elementHom.toMonoidHom m 1 (A*z₁) n*HeckeFamily.elementCoeff τ n)
    (hx : FixedInducingRow η₁ Q m A z₁) : FixedInducingRow η₂ Q m A z₂ := by
  obtain ⟨χ,ψ,hχk,hψk,hprim,hind,hQ,hrow⟩ := hx
  obtain ⟨ρ,hρk,hρ,hQρ,hindρ⟩ := fixed_primitive_finite_product χ ψ
    (hψk.trans hχk.symm) τ hind Q hQ hτ
  refine ⟨finiteTwist χ τ,ρ,hχk.trans htype.symm,
    hρk.trans (hχk.trans htype.symm),hρ,hindρ,hQρ,?_⟩
  intro n
  rw [elementCoeff_finiteTwist,hrow n,he n]

theorem childCharacter_ratio (η : AngularCharacter) (χ ξ : RayCharacter) (n : O) :
    (childCharacter η ξ).elementCoeff n=
      (childCharacter η χ).elementCoeff n*HeckeFamily.elementCoeff (rayRatio χ ξ) n := by
  have h := CenteredMomentExceptionalPair.childCharacter_ratio finiteTrivial χ ξ n
  simp only [CenteredMomentChildRows.childCharacter,HeckeFamily.elementCoeff_product,
    finiteTrivial_elementCoeff,one_mul] at h
  simp only [childCharacter,elementCoeff_finiteTwist]
  rw [h]
  ring

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixed_primitive_finite_product
