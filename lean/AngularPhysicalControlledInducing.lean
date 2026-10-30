import AngularPhysicalExceptionalSupport
import AngularPhysicalVolumeHeight

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
local notation "O" => ActualEisensteinCubic.O

theorem idealHom_ne_zero_iff (χ : AngularCharacter) (I : Ideal O) :
    χ.idealHom I ≠ 0 ↔ I ≠ ⊥ ∧ IsCoprime I χ.modulus := by
  simp only [ne_eq, χ.idealHom_zero_iff, not_or, not_not]

theorem inducedBy_of_elementCoeff_eq (χ χ' ψ : AngularCharacter)
    (heq : ∀ n, χ'.elementCoeff n=χ.elementCoeff n)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  have hideal (I : Ideal O) : χ'.idealHom I=χ.idealHom I := by
    conv_lhs => rw [← Ideal.span_singleton_generator I, χ'.idealHom_span, heq]
    rw [← χ.idealHom_span, Ideal.span_singleton_generator]
  intro I
  by_cases hI : I=0
  · simp only [hI, map_zero, ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn := (idealHom_ne_zero_iff χ' I).mpr ⟨hI,hc⟩
    rw [hideal I] at hn
    have hc' := (idealHom_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc, hideal I, hind I, ite_eq_left hc']
  · have hz : χ'.idealHom I=0 := by
      by_contra hn
      exact hc ((idealHom_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixedInducingRow_controlled (η : AngularCharacter) (Q : Ideal O) (m A₀ z : O)
    (hm : m ≠ 0) (hA : A₀ ≠ 0) (hz : z ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hex : FixedInducingRow η Q m A₀ z) :
    ∃ χ ψ : AngularCharacter, χ.k=η.k ∧ ψ.k=η.k ∧
      χ.modulus.absNorm ≤ AngularRowClosure.rowConductorBound η m 1 (A₀*z) ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
      ∀ n, χ.elementCoeff n=CanonicalRowCompletion.rowTwist
        η.elementHom.toMonoidHom m 1 (A₀*z) n := by
  obtain ⟨χ₀,ψ,_,hψk,hprim,hind,hQ,hrow₀⟩ := hex
  obtain ⟨χ,hχk,hbound,hrow,_⟩ := AngularRowClosure.exists_angular_row_character
    η m 1 (A₀*z) hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2
  refine ⟨χ,ψ,hχk,hψk,hbound,hprim,?_,hQ,hrow⟩
  exact inducedBy_of_elementCoeff_eq χ₀ χ ψ (fun n => (hrow n).trans (hrow₀ n).symm) hind

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixedInducingRow_controlled
