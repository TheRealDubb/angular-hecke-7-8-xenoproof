import AngularPhysicalChildRows
import OAI.NumberTheory.DirichletL.Moments.NonprincipalGate

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
open CanonicalRowCompletion ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def unitCharacter : AngularCharacter :=
  AngularCharacter.ofFinite CenteredMomentNonprincipalGate.unitCharacter

theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue :=
  CenteredMomentNonprincipalGate.unitCharacter_primitive

theorem unitCharacter_ideal (I : Ideal O) (hI : I≠0) : unitCharacter.idealHom I=1 := by
  rw [unitCharacter, AngularCharacter.ofFinite_idealHom]
  exact CenteredMomentNonprincipalGate.unitCharacter_ideal I hI

theorem principal_inducedBy_unit (χ : AngularCharacter) (hk : χ.k=0) (hχ : χ.residue=1) :
    InducedBy χ unitCharacter := by
  intro I
  by_cases hI : I=0
  · subst I
    simp only [map_zero,ite_self]
  · have hn := idealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_idealGenerator I,χ.idealHom_span,χ.elementCoeff_eq hn,hk,zpow_zero,one_mul,hχ]
    by_cases hc : IsCoprime (Ideal.span {idealGenerator I}) χ.modulus
    · rw [ite_eq_left hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [ite_eq_right hc]
      exact MulChar.map_nonunit _ (fun h => hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))

theorem principal_row_fixed (η χ : AngularCharacter) (htype : χ.k=η.k)
    (Q : Ideal O) (m A z : O)
    (hrow : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hk : χ.k=0) (hχ : χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,htype,hk.symm.trans htype,unitCharacter_primitive,
    principal_inducedBy_unit χ hk hχ,le_top,hrow⟩

theorem actual_row_nonprincipal (η χ : AngularCharacter) (htype : χ.k=η.k)
    (Q : Ideal O) (m A z : O)
    (hrow : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hex : ¬FixedInducingRow η Q m A z) : χ.k≠0 ∨ χ.residue≠1 := by
  by_cases hk : χ.k=0
  · exact Or.inr (fun h => hex (principal_row_fixed η χ htype Q m A z hrow hk h))
  · exact Or.inl hk

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.actual_row_nonprincipal
