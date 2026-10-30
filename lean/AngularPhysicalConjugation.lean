import AngularPhysicalScale
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import OAI.NumberTheory.DirichletL.Hecke.Conjugation
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.Angular.InverseAmplification
open OAI.SevenEighths.Angular.Dyadic

theorem coefficient_conjugate (χ : AngularCharacter) (inv : Bool) (J : Ideal O) :
    coefficient χ.conjugate inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,AngularCharacter.conjugate_idealHom,star_def]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (shift σ freq)=shift σ (-freq) := by
  simp only [Dyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : AngularCharacter) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.conjugate inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_conjugate]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : AngularCharacter) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.conjugate inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

#print axioms polynomial_inverse_norm
end SevenEighths.Angular.InverseAmplification
end
end OAI
