import AngularPhysicalFinite
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePlain

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.Angular.InverseAmplification
open OAI.SevenEighths.Angular.Dyadic HeckeDetectorRowwise

open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support)

def scaleSum (χ : AngularCharacter) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleSum_continuous (χ : AngularCharacter) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : AngularCharacter) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ W S) (scaleSum χ (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ true J) using 1
    · rfl
    · change coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ true J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

theorem scaleSum_eq_polynomial (χ : AngularCharacter) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ W S l=polynomial χ true W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ true W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [Dyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

#print axioms scaleSum_deriv
#print axioms scaleSum_eq_polynomial
end SevenEighths.Angular.InverseAmplification

end

end OAI
