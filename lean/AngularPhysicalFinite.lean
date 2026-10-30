import AngularPhysicalPolynomial
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.Dyadic
open UniqueFactorizationMonoid
lemma polynomial_eq_finite (χ : AngularCharacter) (inverse : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (S : Finset (Ideal O))
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ J∈S,
        coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
          (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  let f : Ideal O→ℂ := fun J => coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
    (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)
  have hf : Function.support f ⊆ {J : Ideal O | J≠0} := by
    intro J hJ hzero
    subst J
    apply hJ
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have he := tsum_subtype_eq_of_support_subset hf
  change (∑' J : {J : Ideal O // J≠0}, f J.val)=_
  apply he.trans
  apply tsum_eq_sum
  intro J hJ
  by_cases hj : J=0
  · subst J
    dsimp only [f]
    rw [coefficient_zero, zero_mul, zero_mul]
  have hw : W ((J.absNorm : ℝ)/D)=0 := by
    by_contra hw
    exact hJ (hcover J hj hw)
  simp [f,hw]

theorem phase_sum_eq_polynomial (χ : AngularCharacter) (inverse : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (s : ℂ) (t : ℝ) (S : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    (∑ J∈S, coefficient χ inverse J*(J.absNorm : ℂ)^(-s)*
      W ((J.absNorm : ℝ)/D)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ inverse W D s.re (2*Real.pi*t-s.im) := by
  rw [polynomial_eq_finite χ inverse W D s.re (2*Real.pi*t-s.im) S hcover,
    ← mul_assoc, HeckeDetectorDyadicBridge.normalization D hD s, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hnorm : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS J hJ))
  have hp := HeckeDetectorDyadicBridge.norm_phase (J.absNorm : ℝ) D hnorm hD s t
  simp only [Complex.ofReal_natCast] at hp
  calc
    _ = coefficient χ inverse J*W ((J.absNorm : ℝ)/D)*
        ((J.absNorm : ℂ)^(-s)*FourierBridge.logPhase t (Real.log ((J.absNorm : ℝ)/D))) := by ring
    _ = _ := by rw [hp]; simp only [HeckeDyadic.shift, shift]; ring

theorem polynomial_all_ideals (χ:AngularCharacter)(W:ℝ→ℂ)(X σ t:ℝ):
    polynomial χ true W X σ t=(X:ℂ)^(-(1/2:ℂ))*
      ∑'I:Ideal O,(moebius I:ℂ)*χ.idealHom I*
        (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t)) := by
  unfold polynomial
  congr 1
  let f:Ideal O→ℂ:=fun I=>(moebius I:ℂ)*χ.idealHom I*
    (W ((I.absNorm:ℝ)/X)*(((I.absNorm:ℝ)/X:ℝ):ℂ)^(-shift σ t))
  have hf:Function.support f⊆{I:Ideal O|I≠0}:=by
    intro I hi hz
    subst I
    exact hi (by simp only [f,map_zero,mul_zero,zero_mul])
  have he:=tsum_subtype_eq_of_support_subset hf
  calc
    _=∑'I:{I:Ideal O//I≠0},f I.val:=by
      apply tsum_congr
      intro I
      simp only [summand,coefficient,ite_true,norm,f]
      ring
    _=_:=he


#print axioms polynomial_eq_finite
#print axioms phase_sum_eq_polynomial
#print axioms polynomial_all_ideals
end OAI.SevenEighths.Angular.Dyadic
