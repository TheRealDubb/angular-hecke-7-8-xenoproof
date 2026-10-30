import AngularPhysicalRelativeFiniteProduct
import OAI.NumberTheory.DirichletL.Hecke.RayQuotient

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.RelativePrime
local notation "O" => ActualEisensteinCubic.O

def internalQ (Q:Ideal O) (Ω:AngularCharacter) : Ideal O := Q⊓Ω.modulus

variable (M:Ideal O) [NeZero M]
local instance angularFixedAnchorFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

def rayRelativeCharacter (Ω:AngularCharacter) (θ:RayQuotient.Characters M H) : AngularCharacter :=
  relativeCharacter Ω (HeckeRayQuotient.character M H hH θ)

theorem rayRelativeCharacter_k (Ω:AngularCharacter) (θ:RayQuotient.Characters M H) :
    (rayRelativeCharacter M H hH Ω θ).k= -Ω.k :=
  relativeCharacter_k Ω _

theorem rayRelativeCharacter_modulus (Ω:AngularCharacter) (θ:RayQuotient.Characters M H) :
    (rayRelativeCharacter M H hH Ω θ).modulus=Ω.modulus⊓M := rfl

/-- The support zeros of the anchor and the fixed ray coefficient are both retained. -/
theorem rayRelativeCharacter_coeff (Ω:AngularCharacter) (θ:RayQuotient.Characters M H) (I:Ideal O) :
    (rayRelativeCharacter M H hH Ω θ).idealHom I=
      star (Ω.idealHom I)*RayQuotient.idealCharacter M H hH θ I :=
  relativeCharacter_coeff Ω _ I

theorem internalQ_le_relative_modulus (Q:Ideal O) (hQM:Q≤M)
    (Ω:AngularCharacter) (θ:RayQuotient.Characters M H) :
    internalQ Q Ω≤(rayRelativeCharacter M H hH Ω θ).modulus := by
  rw [rayRelativeCharacter_modulus]
  exact le_inf inf_le_right (inf_le_left.trans hQM)

theorem ray_inverse_anchor_cancels_type (Ω η:AngularCharacter) (hη:η.k=Ω.k)
    (θ:RayQuotient.Characters M H) : η.k+(rayRelativeCharacter M H hH Ω θ).k=0 :=
  inverse_anchor_cancels_type Ω η hη _

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.rayRelativeCharacter_k
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.rayRelativeCharacter_k

#print axioms OAI.SevenEighths.Angular.RelativePrime.rayRelativeCharacter_modulus
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.rayRelativeCharacter_modulus

#print axioms OAI.SevenEighths.Angular.RelativePrime.rayRelativeCharacter_coeff
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.rayRelativeCharacter_coeff

#print axioms OAI.SevenEighths.Angular.RelativePrime.internalQ_le_relative_modulus
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.internalQ_le_relative_modulus

#print axioms OAI.SevenEighths.Angular.RelativePrime.ray_inverse_anchor_cancels_type
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.ray_inverse_anchor_cancels_type
