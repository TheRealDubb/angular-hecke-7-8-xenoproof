import AngularPhysicalDeletion
import AngularPhysicalPrimeMask
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows

/- The prime-column identity is obtained from the finite Möbius deletion
   formula. No reciprocal L-function or contour identity is a premise. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex UniqueFactorizationMonoid
namespace SevenEighths.Angular.InverseAmplification
open OAI.SevenEighths.Angular.Dyadic
open IdealMobiusDivisorSum

theorem prime_column_identity (χ ψ : AngularCharacter)
    (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : ψ.idealHom = IdealEuler.deletePrimes {P} χ.idealHom)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ true W D σ freq = polynomial ψ true W D σ freq -
      χ.idealHom P.val * (P.val.absNorm : ℂ) ^ (-(1/2 : ℂ)) *
        polynomial ψ true W (D / (P.val.absNorm : ℝ)) σ freq := by
  let hS : ∀ Q ∈ ({P.val} : Finset (Ideal O)), Prime Q := by
    intro Q hQ
    simpa only [Finset.mem_singleton.mp hQ] using P.property
  have hψ : (χ.excludePrimes {P.val} hS).idealHom = ψ.idealHom := by
    ext J
    rw [AngularCharacter.idealHom_excludePrimes, hm, IdealEuler.deletePrimes_apply]
    simp [InverseRows.prime_coprime_iff]
  have hpoly (Y : ℝ) :
      polynomial (χ.excludePrimes {P.val} hS) true W Y σ freq =
        polynomial ψ true W Y σ freq := by
    unfold polynomial
    simp only [summand, coefficient, hψ]
  have hd : idealDivisors P.val = {1, P.val} := by
    ext J
    rw [mem_idealDivisors P.property.ne_zero,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hJ
      obtain ⟨j, hj, he⟩ := (dvd_prime_pow P.property 1).mp (by simpa using hJ)
      have heq := associated_iff_eq.mp he
      interval_cases j
      · exact Or.inl (by simpa using heq)
      · exact Or.inr (by simpa using heq)
    · rintro (rfl | rfl)
      · exact one_dvd _
      · exact dvd_refl _
  have hP1 : P.val ≠ 1 := fun h => P.property.not_isUnit (h ▸ isUnit_one)
  have he := InverseDeletion.inverse_polynomial_decomposition χ {P.val} hS W
    D σ freq b hD (fun x hx => (hWs hx).2)
  simp only [Finset.prod_singleton] at he
  rw [hd, Finset.sum_insert (by simpa using Ne.symm hP1), Finset.sum_singleton] at he
  simp only [moebius_one, map_one] at he
  simpa [hP1, Ne.symm hP1, P.property.irreducible.moebius_eq,
    hpoly, sub_eq_add_neg] using he

#print axioms prime_column_identity
end SevenEighths.Angular.InverseAmplification
end
end OAI
