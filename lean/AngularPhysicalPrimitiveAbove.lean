import AngularPhysicalNonprincipalGate
import OAI.NumberTheory.DirichletL.Hecke.MaskDescent

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
local notation "O" => ActualEisensteinCubic.O

theorem exists_primitive_above (χ : AngularCharacter) (Q : Ideal O)
    (hdesc : FiniteConductor.FactorsThroughIdeal χ.residue
      (Q.map (Ideal.Quotient.mk χ.modulus))) :
    ∃ ψ : AngularCharacter, ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨K,φ,hMK,hQK,hK,hprim,hnorm,hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation_above_quotient
      χ.modulus χ.residue (Q.map (Ideal.Quotient.mk χ.modulus)) hdesc
  have hu : ∀ u : Oˣ, alpha (u:O)^χ.k * φ (Ideal.Quotient.mk K (u:O))=1 := by
    intro u
    have h := hmask (u:O)
    simp only [u.isUnit.map (Ideal.Quotient.mk χ.modulus),ite_true] at h
    rw [←h]
    exact χ.unit_compatible u
  let ψ : AngularCharacter := ⟨χ.k,K,hK,φ,hu⟩
  refine ⟨ψ,rfl,hprim,(Ideal.le_comap_map).trans hQK,?_⟩
  intro I
  rw [←Ideal.span_singleton_generator I,χ.idealHom_span,ψ.idealHom_span]
  by_cases hg : Submodule.IsPrincipal.generator I=0
  · rw [hg,χ.elementCoeff_zero,ψ.elementCoeff_zero]
    simp only [ite_self]
  · rw [χ.elementCoeff_eq hg,ψ.elementCoeff_eq hg]
    change alpha _^χ.k * χ.residue _ =
      if IsCoprime (Ideal.span {Submodule.IsPrincipal.generator I}) χ.modulus
      then alpha _^χ.k * φ _ else 0
    rw [hmask]
    simp only [IdealCharacter.isUnit_mk_iff_isCoprime]
    split_ifs <;> first | rfl | exact mul_zero _

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.exists_primitive_above
