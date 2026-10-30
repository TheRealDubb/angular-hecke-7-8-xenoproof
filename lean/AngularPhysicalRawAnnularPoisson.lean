import AngularPhysicalAnnularScaledFourier
import OAI.NumberTheory.DirichletL.TraceCharacter

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularReflection
open EisensteinSchwartzPoisson AnnularSchwartz AnnularFourier PlaneVolume ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

variable (c:O) [instc:NeZero c]

def rawCoefficient (k:ℤ) (ρ:MulChar (O⧸Ideal.span {c}) ℂ) (z:O) : ℂ :=
  if z=0 then 0 else alpha z^k*ρ (Ideal.Quotient.mk (Ideal.span {c}) z)

theorem raw_source_term (k:ℤ) (ρ:MulChar (O⧸Ideal.span {c}) ℂ)
    (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (X:ℝ) (hX:0<X) (z:O) :
    ρ (Ideal.Quotient.mk (Ideal.span {c}) z)*
      scaledPlane (annularCLM k a b ha W) X hX (eisEmbedding z)=
      rawCoefficient c k ρ z*W (‖eisEmbedding z‖^2/X) := by
  rw [scaledPlane_apply,annularCLM_scaled k a b ha W hs X hX]
  by_cases hz:z=0
  · subst z
    have hw:W 0=0:=by
      by_contra h
      have hh: a≤0:=(hs h).1
      linarith
    simp [rawCoefficient,hw]
  · rw [rawCoefficient,if_neg hz]
    change ρ (Ideal.Quotient.mk _ z)*(alpha z^k*W _)=_
    ring

theorem primitive_raw_annular_poisson (k:ℤ) (ρ:MulChar (O⧸Ideal.span {c}) ℂ)
    (hρ:FiniteFourier.IsPrimitiveOnIdeals ρ) (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (hz:ρ⁻¹ 0*paperFourier (annularCLM k a b ha W) 0=0)
    (X:ℝ) (hX:0<X) :
    (∑'z:O,rawCoefficient c k ρ z*W (‖eisEmbedding z‖^2/X))=
      ((X:ℂ)*alpha c^k*TraceCharacter.gaussScalar c ρ/(Ideal.absNorm (Ideal.span {c}):ℂ))*
      ∑'z:O,rawCoefficient c (-k) ρ⁻¹ z*
        profile k a b ha W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
  have hp:=TraceCharacter.primitive_paper_poisson c
    (scaledPlane (annularCLM k a b ha W) X hX) ρ hρ
  simp_rw [raw_source_term c k ρ a b ha W hs X hX] at hp
  rw [hp,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro z
  by_cases hz0:z=0
  · subst z
    simp only [map_zero,zero_div]
    rw [scaledPlane_fourier,mul_zero]
    simp only [rawCoefficient,ite_true,zero_mul,mul_zero,Complex.real_smul]
    linear_combination (TraceCharacter.gaussScalar c ρ/(Ideal.absNorm (Ideal.span {c}):ℂ)*(X:ℂ))*hz
  · rw [scaled_fourier_nonzero k a b ha W hs X hX c z (NeZero.ne c) hz0,
      rawCoefficient,if_neg hz0]
    ring

end OAI.SevenEighths.Angular.AnnularReflection

#print axioms OAI.SevenEighths.Angular.AnnularReflection.primitive_raw_annular_poisson
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularReflection.primitive_raw_annular_poisson
