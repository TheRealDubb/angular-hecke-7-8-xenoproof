import AngularPhysicalFinitePrimeCeiling
import OAI.NumberTheory.DirichletL.Moments.PrimeGlobal

noncomputable section
open scoped Classical ContDiff
open Set
namespace OAI.SevenEighths.Angular.RelativePrime
open HeckeFamily HeckePrimeRay

lemma zeroMaximum_le_ceiling {ι:Type*} [Fintype ι]
    (χ:ι→Character) (hχ:∀i,(χ i).residue≠1) (T b:ℝ)
    (hfloor:(51/100:ℝ)≤b) (hceil:HeckeZeroSupremum.beta≤b) :
    HeckeDetectorZeros.zeroMaximum χ hχ T≤b := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact hfloor
  · obtain ⟨⟨i,s⟩,hs,rfl⟩:=Finset.mem_image.mp hx
    have hz:=(HeckeDetectorZeros.mem_familyZeros χ hχ T i s).mp hs
    exact (HeckeZeroSupremum.zero_re_le_beta (χ i) (by linarith [hz.1])
      (Or.inr (hχ i)) hz.2.2.2).trans hceil

variable (M:Ideal O) [NeZero M]
local instance relativePrimeFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O ⧸ M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

theorem ray_prime_ceiling_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e slack η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hslack : 0<slack) (hη : 0≤η)
    (hbudget : 8*e*R+slack≤ε) :
    ∃ C : ℝ,0<C ∧ ∀ b κ : ℝ,(51/100:ℝ)≤b → b≤1 →
      HeckeZeroSupremum.beta≤b → 2*b-1≤κ → ∀ Z d : ℝ,1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (_hn : ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (i : ℕ),
    ∀ r σ freq : ℝ,0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq‖^2≤
        C*(Z^d)^(κ*r+2*ε) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e slack η σmin σmax hR hdmax hτ hε he he' hslack hη hbudget
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro b κ hfloor hupper hceil hκ Z d hZ hd hdmax hU hT χ hn i r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hmax := zeroMaximum_le_ceiling (twistedFamily M H hH χ) hn
    (3*(i+1:ℕ)*Z^τ) b hfloor hceil
  have hb := hbound Z d hZ hd hdmax hU hT χ hn b i hfloor hupper
    (by linarith) r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hUp : 0<Z^d := by linarith
  have hp : ((Z^d)^((b-1/2)*r+ε))^2 = (Z^d)^(2*((b-1/2)*r+ε)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  calc
    _≤(C*(Z^d)^((b-1/2)*r+ε))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _=C^2*(Z^d)^(2*((b-1/2)*r+ε)) := by rw [mul_pow,hp]
    _≤C^2*(Z^d)^(κ*r+2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Z^d)
        (by nlinarith [mul_le_mul_of_nonneg_right hκ hr])) (sq_nonneg _)

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.zeroMaximum_le_ceiling
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.zeroMaximum_le_ceiling

#print axioms OAI.SevenEighths.Angular.RelativePrime.ray_prime_ceiling_squared
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.ray_prime_ceiling_squared
