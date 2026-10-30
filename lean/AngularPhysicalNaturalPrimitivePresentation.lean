import AngularPhysicalNaturalPrimitiveDeletion
import AngularTypeZeroEntire

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalPrimitive
open CenteredMomentNaturalPrimitive
local notation "O" => ActualEisensteinCubic.O

theorem primitive_nonprincipal (χ:AngularCharacter) (hn:χ.k≠0 ∨ χ.residue≠1) :
    (PrimitiveReduction.primitive χ).k≠0 ∨ (PrimitiveReduction.primitive χ).residue≠1 := by
  by_cases hk:χ.k=0
  · exact Or.inr (TypeZeroEntire.primitive_residue_nonprincipal χ hk (hn.resolve_left (not_ne_iff.mpr hk)))
  · exact Or.inl hk

theorem exists_natural_primitive (χ:AngularCharacter) :
    ∃ψ:AngularCharacter, ψ.k=χ.k ∧ χ.modulus≤ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ((χ.k≠0 ∨ χ.residue≠1) → (ψ.k≠0 ∨ ψ.residue≠1)) ∧
      Squarefree (redundantIdeal χ.modulus ψ.modulus) ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      ψ.modulus*redundantIdeal χ.modulus ψ.modulus∣χ.modulus ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀I:Ideal O, χ.idealHom I=(ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
        (redundantSet_prime χ.modulus ψ.modulus)).idealHom I := by
  let ψ:=PrimitiveReduction.primitive χ
  have hm:=PrimitiveReduction.modulus_le χ
  exact ⟨ψ,rfl,hm,PrimitiveReduction.primitive_isPrimitive χ,primitive_nonprincipal χ,
    redundantIdeal_squarefree _ _,redundantIdeal_coprime _ _ ψ.modulus_ne_bot,
    primitive_redundant_dvd _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hm),
    primitive_redundant_norm _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hm),
    idealHom_natural_deletion χ ψ hm (PrimitiveReduction.idealHom_source_mask χ)⟩

end OAI.SevenEighths.Angular.NaturalPrimitive

#print axioms OAI.SevenEighths.Angular.NaturalPrimitive.exists_natural_primitive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalPrimitive.exists_natural_primitive
