import AngularPhysicalPrimitiveAbove
import OAI.NumberTheory.DirichletL.Hecke.PrimeRay

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open AngularRowClosure CanonicalRowCompletion
open PrimaryVolume (InducedBy)
local notation "O" => ActualEisensteinCubic.O

theorem finite_twist_principal_descent (χ : AngularCharacter) (θ : HeckeFamily.Character)
    (hp : (finiteTwist χ θ).residue=1) :
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
  have hcp : IsCoprime (Ideal.span {a}) (finiteTwist χ θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv : (finiteTwist χ θ).residue (Ideal.Quotient.mk (finiteTwist χ θ).modulus a)=1 := by
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  change ResidueCharacter.product χ.modulus θ.modulus χ.residue θ.residue
    (Ideal.Quotient.mk (χ.modulus ⊓ θ.modulus) a)=1 at hv
  rw [ResidueCharacter.product_mk,ha,hθa,map_one,mul_one] at hv
  exact hv

theorem finite_twist_principal_inducing (χ : AngularCharacter) (θ : HeckeFamily.Character)
    (hp : (finiteTwist χ θ).residue=1) :
    ∃ ψ : AngularCharacter, ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  exists_primitive_above χ θ.modulus (finite_twist_principal_descent χ θ hp)

theorem actual_row_finite_twist_nonprincipal (η χ : AngularCharacter) (htype : χ.k=η.k)
    (θ : HeckeFamily.Character) (Q : Ideal O) (m A z : O)
    (hrow : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hQ : Q≤θ.modulus) (hex : ¬FixedInducingRow η Q m A z) :
    (finiteTwist χ θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψk,hψ,hmod,hind⟩ := finite_twist_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,htype,hψk.trans htype,hψ,hind,hQ.trans hmod,hrow⟩

variable (M : Ideal O) [instM : NeZero M]
local instance angularNonprincipalQuotientFinite : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem all_ray_twists_nonprincipal (η χ : AngularCharacter) (htype : χ.k=η.k)
    (Q : Ideal O) (m A z : O)
    (hrow : ∀ n : O, χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hQ : Q≤M) (hex : ¬FixedInducingRow η Q m A z) :
    ∀ θ : RayQuotient.Characters M H,
      (finiteTwist χ (HeckeRayQuotient.character M H hH θ)).residue≠1 := by
  intro θ
  exact actual_row_finite_twist_nonprincipal η χ htype (HeckeRayQuotient.character M H hH θ)
    Q m A z hrow hQ hex

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.all_ray_twists_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.all_ray_twists_nonprincipal
