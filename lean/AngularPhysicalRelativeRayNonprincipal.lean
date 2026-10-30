import AngularPhysicalRelativeFiniteProduct
import OAI.NumberTheory.DirichletL.Hecke.PrimeRay

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.RelativePrime
open ExceptionalRows
local notation "O" => ActualEisensteinCubic.O

/-- A principal ray twist of the canceled product forces the parent residue
to descend through the full fixed intersection, not just the ray modulus. -/
theorem twisted_relative_principal_descent (χ ν:AngularCharacter) (hk:χ.k+ν.k=0)
    (θ:HeckeFamily.Character) (hp:((finiteProduct χ ν hk).product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      ((ν.modulus⊓θ.modulus).map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O⧸χ.modulus):=Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩:=(Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a:O:=1+q
  have ha:Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus):=by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hνa:Ideal.Quotient.mk ν.modulus a=1:=by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr (show q∈ν.modulus from hq.1),add_zero]
  have hθa:Ideal.Quotient.mk θ.modulus a=1:=by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr (show q∈θ.modulus from hq.2),add_zero]
  have hcχ:IsCoprime (Ideal.span {a}) χ.modulus:=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcν:IsCoprime (Ideal.span {a}) ν.modulus:=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hνa ▸ isUnit_one)
  have hcθ:IsCoprime (Ideal.span {a}) θ.modulus:=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcρ:IsCoprime (Ideal.span {a}) (finiteProduct χ ν hk).modulus:=
    (hcχ.mul_right hcν).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hcp:IsCoprime (Ideal.span {a}) ((finiteProduct χ ν hk).product θ).modulus:=
    (hcρ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv:((finiteProduct χ ν hk).product θ).residue
      (Ideal.Quotient.mk ((finiteProduct χ ν hk).product θ).modulus a)=1:=by
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  change ResidueCharacter.product (finiteProduct χ ν hk).modulus θ.modulus
    (finiteProduct χ ν hk).residue θ.residue
    (Ideal.Quotient.mk ((finiteProduct χ ν hk).modulus⊓θ.modulus) a)=1 at hv
  rw [ResidueCharacter.product_mk,hθa,map_one,mul_one] at hv
  change ResidueCharacter.product χ.modulus ν.modulus χ.residue ν.residue
    (Ideal.Quotient.mk (χ.modulus⊓ν.modulus) a)=1 at hv
  rw [ResidueCharacter.product_mk,ha,hνa,map_one,mul_one] at hv
  exact hv

theorem actual_row_relative_ray_nonprincipal (η χ ν:AngularCharacter)
    (htype:χ.k=η.k) (hk:χ.k+ν.k=0) (θ:HeckeFamily.Character)
    (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,χ.elementCoeff n=CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hQν:Q≤ν.modulus) (hQθ:Q≤θ.modulus)
    (hex:¬FixedInducingRow η Q m A z) :
    ((finiteProduct χ ν hk).product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψk,hψ,hmod,hind⟩:=exists_primitive_above χ (ν.modulus⊓θ.modulus)
    (twisted_relative_principal_descent χ ν hk θ hp)
  exact hex ⟨χ,ψ,htype,hψk.trans htype,hψ,hind,(le_inf hQν hQθ).trans hmod,hrow⟩

variable (M:Ideal O) [instM:NeZero M]
local instance relativeRayGateFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

theorem all_relative_ray_twists_nonprincipal (η χ ν:AngularCharacter)
    (htype:χ.k=η.k) (hk:χ.k+ν.k=0) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,χ.elementCoeff n=CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hQν:Q≤ν.modulus) (hQM:Q≤M) (hex:¬FixedInducingRow η Q m A z) :
    ∀θ:RayQuotient.Characters M H,
      (HeckePrimeRay.twistedFamily M H hH (finiteProduct χ ν hk) θ).residue≠1 := by
  intro θ
  exact actual_row_relative_ray_nonprincipal η χ ν htype hk
    (HeckeRayQuotient.character M H hH θ) Q m A z hrow hQν hQM hex

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.twisted_relative_principal_descent
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.twisted_relative_principal_descent

#print axioms OAI.SevenEighths.Angular.RelativePrime.actual_row_relative_ray_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.actual_row_relative_ray_nonprincipal

#print axioms OAI.SevenEighths.Angular.RelativePrime.all_relative_ray_twists_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.all_relative_ray_twists_nonprincipal
