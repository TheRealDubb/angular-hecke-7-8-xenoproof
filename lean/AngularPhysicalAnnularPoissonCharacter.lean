import AngularPhysicalRawAnnularPoisson

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularReflection
open EisensteinSchwartzPoisson AnnularSchwartz AnnularFourier ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal
variable (c:O) [instc:NeZero c]

theorem rawCoefficient_actual (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c}) (z:O) :
    rawCoefficient c ψ.k (hmod ▸ ψ.residue) z=ψ.elementCoeff z := by
  cases ψ
  cases hmod
  rfl

theorem rawCoefficient_conjugate (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c}) (z:O) :
    rawCoefficient c (-ψ.k) (hmod ▸ ψ.residue)⁻¹ z=ψ.conjugate.elementCoeff z := by
  letI:Finite (O⧸ψ.modulus):=Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  have he:(hmod ▸ ψ.residue)⁻¹=(hmod ▸ ψ.conjugate.residue) := by
    cases ψ
    cases hmod
    simp only [AngularCharacter.conjugate,MulChar.star_eq_inv]
    rfl
  rw [he]
  exact rawCoefficient_actual c ψ.conjugate hmod z

theorem primitive_zero_mode (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c})
    (hn:ψ.k≠0 ∨ ψ.residue≠1) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) :
    (hmod ▸ ψ.residue)⁻¹ 0*paperFourier (annularCLM ψ.k a b ha W) 0=0 := by
  rcases hn with hk|hρ
  · rw [nonzero_order_fourier_zero ψ.k hk a b ha W hs,mul_zero]
  · have hρ':(hmod ▸ ψ.residue)≠1:=by cases ψ; cases hmod; exact hρ
    letI:Nontrivial (O⧸Ideal.span {c}):=
      CenteredMomentComparisonReflection.residue_nontrivial c (hmod ▸ ψ.residue) hρ'
    rw [MulChar.map_zero,zero_mul]

def annularReflectionScalar (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c}) : ℂ :=
  alpha c^ψ.k*TraceCharacter.normalizedGauss c (hmod ▸ ψ.residue)

theorem norm_annularReflectionScalar (ψ:AngularCharacter) (hmod:ψ.modulus=Ideal.span {c})
    (hp:FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ ψ.residue)) :
    ‖annularReflectionScalar c ψ hmod‖=1 := by
  rw [annularReflectionScalar,norm_mul,norm_zpow,norm_alpha (NeZero.ne c),one_zpow,
    TraceCharacter.normalizedGauss_norm c _ hp,one_mul]

end OAI.SevenEighths.Angular.AnnularReflection

#print axioms OAI.SevenEighths.Angular.AnnularReflection.primitive_zero_mode
#print axioms OAI.SevenEighths.Angular.AnnularReflection.norm_annularReflectionScalar
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularReflection.norm_annularReflectionScalar
