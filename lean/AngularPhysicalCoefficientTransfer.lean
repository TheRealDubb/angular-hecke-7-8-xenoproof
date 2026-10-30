import AngularPhysicalConjugation
import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.Angular.CoefficientTransfer
open OAI.SevenEighths.Angular.Dyadic InverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : AngularCharacter)
    (hc : ∀ J : Ideal O,χ.idealHom J=ψ.idealHom J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

open HeckeDetectorCoefficientTransfer (orientedProfile orientedFrequency)

theorem norm_of_oriented_coefficients (χ ψ : AngularCharacter) (reverse : Bool)
    (hc : ∀ J : Ideal O,χ.idealHom J=
      if reverse then conj (ψ.idealHom J) else ψ.idealHom J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,χ.idealHom J=ψ.conjugate.idealHom J := by
      intro J
      simpa only [Bool.true_eq,ite_true,AngularCharacter.conjugate_idealHom,star_def] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.conjugate hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

#print axioms norm_of_oriented_coefficients
end SevenEighths.Angular.CoefficientTransfer
end
end OAI
