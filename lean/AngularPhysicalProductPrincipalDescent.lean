import AngularPhysicalRayNonprincipal

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open AngularRowClosure CanonicalRowCompletion
open PrimaryVolume (InducedBy)
local notation "O" => ActualEisensteinCubic.O

theorem product_principal_descent (χ : AngularCharacter) (θ : AngularCharacter)
    (hp : (χ.product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (θ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus) := by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hθa : Ideal.Quotient.mk θ.modulus a=1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  have hcχ : IsCoprime (Ideal.span {a}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcθ : IsCoprime (Ideal.span {a}) θ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcp : IsCoprime (Ideal.span {a}) (χ.product θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv : (χ.product θ).residue (Ideal.Quotient.mk (χ.product θ).modulus a)=1 := by
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  change ResidueCharacter.product χ.modulus θ.modulus χ.residue θ.residue
    (Ideal.Quotient.mk (χ.modulus ⊓ θ.modulus) a)=1 at hv
  rw [ResidueCharacter.product_mk,ha,hθa,map_one,mul_one] at hv
  exact hv

theorem product_principal_inducing (χ : AngularCharacter) (θ : AngularCharacter)
    (hp : (χ.product θ).residue=1) :
    ∃ ψ : AngularCharacter, ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  exists_primitive_above χ θ.modulus (product_principal_descent χ θ hp)

theorem actual_row_product_nonprincipal (η χ : AngularCharacter) (htype : χ.k=η.k)
    (θ : AngularCharacter) (Q : Ideal O) (m A z : O)
    (hrow : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hQ : Q≤θ.modulus) (hex : ¬FixedInducingRow η Q m A z) :
    (χ.product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψk,hψ,hmod,hind⟩ := product_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,htype,hψk.trans htype,hψ,hind,hQ.trans hmod,hrow⟩

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.product_principal_descent
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.product_principal_descent

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.product_principal_inducing
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.product_principal_inducing

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.actual_row_product_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.actual_row_product_nonprincipal
