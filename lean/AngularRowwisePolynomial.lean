import AngularPhysicalFinite
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePolynomial
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Set Complex
namespace SevenEighths.Angular.RowwisePolynomial
open OAI.SevenEighths.Angular.Dyadic

open HeckeDetectorRowwisePolynomial (logProfile logProfile_cover
  logProfile_support logProfile_smooth power_sigma_deriv power_freq_deriv)

theorem polynomial_sigma_deriv (χ : AngularCharacter) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D u freq)
      (-polynomial χ inv (logProfile W) D σ freq) σ := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-Dyadic.shift u freq))
      (-coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-Dyadic.shift σ freq)) σ := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,neg_zero] using hasDerivAt_const σ (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_sigma_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    all_goals simp only [Dyadic.shift,HeckeDyadic.shift,logProfile]
    all_goals ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem polynomial_freq_deriv (χ : AngularCharacter) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D σ u)
      (I*polynomial χ inv (logProfile W) D σ freq) freq := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-Dyadic.shift σ u))
      (I*(coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-Dyadic.shift σ freq))) freq := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,mul_zero] using hasDerivAt_const freq (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_freq_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    all_goals simp only [Dyadic.shift,HeckeDyadic.shift,logProfile]
    all_goals ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,←Finset.mul_sum]
  ring

theorem polynomial_continuous (χ : AngularCharacter) (inv : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    Continuous (fun p : ℝ×ℝ => polynomial χ inv W D p.1 p.2) := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro J hJ
  by_cases hz : J=0
  · subst J
    simp only [coefficient_zero,zero_mul]
    exact continuous_const
  have hn : 0<(J.absNorm : ℝ)/D := div_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
  unfold Dyadic.shift
  fun_prop

#print axioms polynomial_sigma_deriv
#print axioms polynomial_freq_deriv
#print axioms polynomial_continuous
end SevenEighths.Angular.RowwisePolynomial

end

end OAI
