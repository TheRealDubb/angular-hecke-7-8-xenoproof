import AngularPhysicalProductPrincipalDescent
import AngularTypeZeroEntire
import AngularPhysicalNaturalRow

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.RelativePrime
local notation "O" => ActualEisensteinCubic.O

/-- The product includes both original moduli and every coefficient zero. -/
def finiteProduct (χ ν:AngularCharacter) (hk:χ.k+ν.k=0) : HeckeFamily.Character :=
  FiniteIdentification.toFinite (χ.product ν) hk

theorem finiteProduct_idealCoeff (χ ν:AngularCharacter) (hk:χ.k+ν.k=0) (I:Ideal O) :
    HeckeFamily.idealCoeff (finiteProduct χ ν hk) I=χ.idealHom I*ν.idealHom I := by
  calc
    _=(χ.product ν).idealHom I :=
      congrArg (fun f : Ideal O →*₀ ℂ => f I) (TypeZeroEntire.finite_idealCoeff (χ.product ν) hk)
    _=_ := AngularCharacter.product_idealHom χ ν I

theorem finiteProduct_modulus (χ ν:AngularCharacter) (hk:χ.k+ν.k=0) :
    (finiteProduct χ ν hk).modulus=χ.modulus⊓ν.modulus := rfl

theorem finiteProduct_modulus_bound (χ ν:AngularCharacter) (hk:χ.k+ν.k=0) :
    (finiteProduct χ ν hk).modulus.absNorm≤χ.modulus.absNorm*ν.modulus.absNorm := by
  let : Finite (O⧸χ.modulus):=Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O⧸ν.modulus):=Ring.HasFiniteQuotients.finiteQuotient ν.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ν.modulus

theorem finiteProduct_nonprincipal (η χ ν:AngularCharacter) (htype:χ.k=η.k)
    (hk:χ.k+ν.k=0) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,χ.elementCoeff n=CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom m 1 (A*z) n)
    (hQ:Q≤ν.modulus) (hex:¬ExceptionalRows.FixedInducingRow η Q m A z) :
    (finiteProduct χ ν hk).residue≠1 :=
  ExceptionalRows.actual_row_product_nonprincipal η χ htype ν Q m A z hrow hQ hex

def relativeCharacter (Ω:AngularCharacter) (θ:HeckeFamily.Character) : AngularCharacter :=
  Ω.conjugate.product (AngularCharacter.ofFinite θ)

theorem relativeCharacter_k (Ω:AngularCharacter) (θ:HeckeFamily.Character) :
    (relativeCharacter Ω θ).k= -Ω.k := by simp [relativeCharacter]

theorem relativeCharacter_coeff (Ω:AngularCharacter) (θ:HeckeFamily.Character) (I:Ideal O) :
    (relativeCharacter Ω θ).idealHom I=star (Ω.idealHom I)*HeckeFamily.idealCoeff θ I := by
  rw [relativeCharacter,AngularCharacter.product_idealHom,AngularCharacter.conjugate_idealHom,
    AngularCharacter.ofFinite_idealHom]
  rfl

theorem inverse_anchor_cancels_type (Ω χ:AngularCharacter) (hχ:χ.k=Ω.k)
    (θ:HeckeFamily.Character) : χ.k+(relativeCharacter Ω θ).k=0 := by
  rw [relativeCharacter_k,hχ]
  omega

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.finiteProduct_idealCoeff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.finiteProduct_idealCoeff

#print axioms OAI.SevenEighths.Angular.RelativePrime.finiteProduct_modulus
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.finiteProduct_modulus

#print axioms OAI.SevenEighths.Angular.RelativePrime.finiteProduct_modulus_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.finiteProduct_modulus_bound

#print axioms OAI.SevenEighths.Angular.RelativePrime.finiteProduct_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.finiteProduct_nonprincipal

#print axioms OAI.SevenEighths.Angular.RelativePrime.relativeCharacter_k
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.relativeCharacter_k

#print axioms OAI.SevenEighths.Angular.RelativePrime.relativeCharacter_coeff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.relativeCharacter_coeff

#print axioms OAI.SevenEighths.Angular.RelativePrime.inverse_anchor_cancels_type
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.inverse_anchor_cancels_type
