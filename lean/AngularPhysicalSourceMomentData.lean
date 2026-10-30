import AngularPhysicalSourceRows
import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData

noncomputable section
open scoped Classical ComplexConjugate
namespace OAI.SevenEighths.Angular.SourceRows
open InverseRows
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (momentElement rayCubeFamily)
open ProbePhysical (fixedSourcePrincipal)
local notation "O" => HeckeFamily.O

theorem inverse_row_twist_moment_coeff (χ : HeckeFamily.Character) (u : FreeRow) (I : Ideal O) :
    (AngularCharacter.ofFinite ((ProbeHighRowFamily.rawRow u).inverse.product χ)).idealHom I=
      conj (((momentData (AngularCharacter.ofFinite χ.inverse)).character (momentElement u)).idealHom I) := by
  rw [AngularCharacter.ofFinite_idealHom,finite_moment_character_coeff]
  exact ProbeHighRowFamily.inverse_row_twist_moment_coeff χ u I

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceDetectorFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow) : Sum Bool (RayQuotient.Characters M H)→AngularCharacter :=
  Sum.elim (fun b=>if b then AngularCharacter.ofFinite (ProbeHighRowFamily.rowCharacter S hS u)
    else (targetRow η u).excludePrimes S hS)
    (fun θ=>AngularCharacter.ofFinite (rayCubeFamily M H hH u θ))

def sourceMomentData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : AngularCharacter) :
    Sum Bool (RayQuotient.Characters M H)→RowData :=
  Sum.elim (fun b=>if b then momentData (AngularCharacter.ofFinite (fixedSourcePrincipal S hS))
    else momentData (η.conjugate.excludePrimes S hS))
    (fun θ=>momentData (AngularCharacter.ofFinite (HeckeRayQuotient.character M H hH θ).inverse))

theorem source_family_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    (sourceDetectorFamily M H hH S hS η u j).idealHom I=
      if ProbeHighRowFamily.sourceMomentReverse M H j then
        conj (((sourceMomentData M H hH S hS η j).character (momentElement u)).idealHom I)
      else ((sourceMomentData M H hH S hS η j).character (momentElement u)).idealHom I := by
  rcases j with b|θ
  · cases b
    · simpa [ProbeHighRowFamily.sourceMomentReverse,sourceMomentData,sourceDetectorFamily] using
        denominator_moment_coeff S hS hbad η u I
    · simpa [ProbeHighRowFamily.sourceMomentReverse,sourceMomentData,sourceDetectorFamily] using
        numerator_moment_coeff S hS hbad u I
  · exact inverse_row_twist_moment_coeff (HeckeRayQuotient.character M H hH θ) u I

theorem sourceMomentData_type (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (j : Sum Bool (RayQuotient.Characters M H)) :
    (sourceMomentData M H hH S hS η j).η.k=0 ∨
      (sourceMomentData M H hH S hS η j).η.k= -η.k := by
  rcases j with b|θ
  · cases b <;> simp [sourceMomentData,momentData,AngularCharacter.excludePrimes_k]
  · simp [sourceMomentData,momentData]

theorem sourceMomentData_nonnegative_types (angularOrder : ℕ)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : AngularCharacter)
    (hk : η.k= -(angularOrder:ℤ)) (j : Sum Bool (RayQuotient.Characters M H)) :
    (sourceMomentData M H hH S hS η j).η.k=0 ∨
      (sourceMomentData M H hH S hS η j).η.k=(angularOrder:ℤ) := by
  simpa only [hk,neg_neg] using sourceMomentData_type M H hH S hS η j

theorem source_family_moment_norm (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H))
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖Dyadic.polynomial (sourceDetectorFamily M H hH S hS η u j) inv W D σ freq‖=
      ‖Dyadic.polynomial ((sourceMomentData M H hH S hS η j).character (momentElement u)) inv
        (HeckeDetectorCoefficientTransfer.orientedProfile (ProbeHighRowFamily.sourceMomentReverse M H j) W)
        D σ (HeckeDetectorCoefficientTransfer.orientedFrequency
          (ProbeHighRowFamily.sourceMomentReverse M H j) freq)‖ :=
  CoefficientTransfer.norm_of_oriented_coefficients _ _ _
    (source_family_moment_coeff M H hH S hS hbad η u j) inv W D σ freq hD

#print axioms source_family_moment_coeff
#print axioms sourceMomentData_nonnegative_types
#print axioms source_family_moment_norm
end OAI.SevenEighths.Angular.SourceRows
