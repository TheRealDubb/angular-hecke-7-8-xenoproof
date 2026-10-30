import AngularIdealFactor
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement
import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular
open Submodule.IsPrincipal

def AngularCharacter.refineModulus (χ : AngularCharacter) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ χ.modulus) : AngularCharacter where
  k := χ.k
  modulus := M
  modulus_ne_bot := hM
  residue := ResidueCharacter.inflate hle χ.residue
  unit_compatible u := by
    rw [ResidueCharacter.inflate_mk, ite_eq_left (u.isUnit.map (Ideal.Quotient.mk M))]
    exact χ.unit_compatible u

theorem AngularCharacter.refineModulus_k (χ : AngularCharacter) (M : Ideal O)
    (hM : M ≠ ⊥) (hle : M ≤ χ.modulus) : (χ.refineModulus M hM hle).k = χ.k := rfl

theorem AngularCharacter.elementCoeff_refineModulus (χ : AngularCharacter) (M : Ideal O)
    (hM : M ≠ ⊥) (hle : M ≤ χ.modulus) (a : O) :
    (χ.refineModulus M hM hle).elementCoeff a =
      if IsUnit (Ideal.Quotient.mk M a) then χ.elementCoeff a else 0 := by
  by_cases ha : a = 0
  · subst a
    simp only [AngularCharacter.elementCoeff_zero, ite_self]
  · rw [AngularCharacter.elementCoeff_eq _ ha, AngularCharacter.elementCoeff_eq χ ha]
    change alpha a^χ.k * ResidueCharacter.inflate hle χ.residue (Ideal.Quotient.mk M a) = _
    rw [ResidueCharacter.inflate_mk]
    split_ifs <;> simp

theorem AngularCharacter.idealHom_refineModulus (χ : AngularCharacter) (M : Ideal O)
    (hM : M ≠ ⊥) (hle : M ≤ χ.modulus) (I : Ideal O) :
    (χ.refineModulus M hM hle).idealHom I =
      if IsCoprime I M then χ.idealHom I else 0 := by
  rw [← Ideal.span_singleton_generator I, AngularCharacter.idealHom_span,
    AngularCharacter.elementCoeff_refineModulus, AngularCharacter.idealHom_span]
  simp only [IdealCharacter.isUnit_mk_iff_isCoprime]

def AngularCharacter.excludePrimes (χ : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : AngularCharacter :=
  χ.refineModulus (χ.modulus * ∏ P ∈ S, P)
    (mul_ne_zero χ.modulus_ne_bot (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))
    Ideal.mul_le_left

theorem AngularCharacter.excludePrimes_k (χ : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : (χ.excludePrimes S hS).k = χ.k := rfl

theorem AngularCharacter.idealHom_excludePrimes (χ : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    (χ.excludePrimes S hS).idealHom I =
      if ∀ P ∈ S, IsCoprime I P then χ.idealHom I else 0 := by
  rw [AngularCharacter.excludePrimes, AngularCharacter.idealHom_refineModulus,
    IsCoprime.mul_right_iff, IsCoprime.prod_right_iff]
  by_cases hχ : IsCoprime I χ.modulus
  · simp only [hχ, true_and]
  · have hz : χ.idealHom I = 0 := (χ.idealHom_zero_iff I).mpr (Or.inr hχ)
    simp [hχ, hz]

end OAI.SevenEighths.Angular

namespace OAI.CubicEisenstein.AngularPrimeDeletion
open SevenEighths SevenEighths.Angular CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass InverseInitialExcludedPeriod InverseInitialRayAttachment
open InverseInitialConjugateEnergy AngularCanonicalCoefficient AngularCompletedCoefficient AngularIdealFactor
local notation "Eis" => ActualEisensteinCubic.O

theorem angular_deleted_modulus_proper (χ : AngularCharacter) (q : ℕ) :
    (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus ≠ ⊤ := by
  have htwo : (Ideal.span {(2:Eis)} : Ideal Eis) ∈ reflectionExcludedPrimes q :=
    reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes])
  have hle : (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus ≤
      Ideal.span {(2:Eis)} := by
    change χ.modulus * (∏ P ∈ reflectionExcludedPrimes q, P) ≤ Ideal.span {(2:Eis)}
    exact Ideal.mul_le_right.trans (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P => P) htwo))
  intro he
  exact twoIdeal_maximal.ne_top (top_le_iff.mp (he ▸ hle))

theorem angular_deleted_period_le_modulus (χ : AngularCharacter) (q : ℕ) (hq : q ≠ 0)
    (hp : Ideal.span {(q:Eis)} ≤ χ.modulus) :
    Ideal.span {(deletedPeriod q:Eis)} ≤
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus := by
  change Ideal.span {(deletedPeriod q:Eis)} ≤ χ.modulus * (∏ P ∈ reflectionExcludedPrimes q, P)
  rw [deleted_period_ideal]
  exact Ideal.mul_mono hp (Ideal.dvd_iff_le.mp (excluded_product_divides_reflection q hq))

theorem actual_deleted_conjugate_factor (χ : AngularCharacter) (order q : ℕ)
    (hk : χ.k = (order:ℤ)) (hq : q ≠ 0)
    (hp : Ideal.span {(q:Eis)} ≤ χ.modulus) :
    HasNegativeAngularFactor order (deletedPeriod q)
      (elementCharacter (conjugateIdealCharacter
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).idealHom.toMonoidHom)) := by
  let χd := χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
  have he : elementCharacter (conjugateIdealCharacter χd.idealHom.toMonoidHom) =
      elementCharacter χd.conjugate.idealHom.toMonoidHom := by
    ext a
    exact (χd.conjugate_idealHom (Ideal.span {a})).symm
  rw [he]
  apply actual_negative_ideal_factor χd.conjugate order (deletedPeriod q)
  · simp only [AngularCharacter.conjugate_k, χd, AngularCharacter.excludePrimes_k, hk]
  · right
    let : Nontrivial (Eis ⧸ χd.conjugate.modulus) :=
      Ideal.Quotient.nontrivial_iff.mpr (angular_deleted_modulus_proper χ q)
    change χd.conjugate.residue (Ideal.Quotient.mk χd.conjugate.modulus 0) = 0
    rw [map_zero, MulChar.map_zero]
  · exact Ideal.mul_le_left.trans (angular_deleted_period_le_modulus χ q hq hp)

#print axioms actual_deleted_conjugate_factor
#print axioms angular_deleted_modulus_proper
end OAI.CubicEisenstein.AngularPrimeDeletion
