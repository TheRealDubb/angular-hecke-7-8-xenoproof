import AngularPhysicalFinalAssembly
import AngularNormTwistContinuation

/- The complete real unitary norm-twist family. The released convention is
N^(+i*tau); the research brief uses N^(-i*tau). Both use the same physical
ideal coefficients and have the explicitly shifted principal pole. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex
namespace OAI.SevenEighths.Angular.PhysicalFinalAssembly

theorem norm_twist_nonzero (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (7/8:ℝ)<s.re)
    (hpole : χ.k=0 → χ.residue=1 → s≠1+(τ:ℂ)*I) :
    NormTwist.LFunction χ τ s≠0 := by
  exact LFunction_ne_zero_of_seven_eighths_lt_re χ _ (by simpa using hs)
    (fun hk hr=>(NormTwist.shift_ne_one_iff τ s).mpr (hpole hk hr))

def briefLFunction (χ : AngularCharacter) (τ : ℝ) (s : ℂ) : ℂ :=
  NormTwist.LFunction χ (-τ) s

theorem briefLFunction_eq_shift (χ : AngularCharacter) (τ : ℝ) (s : ℂ) :
    briefLFunction χ τ s=FamilyContinuation.LFunction χ (s+(τ:ℂ)*I) := by
  simp only [briefLFunction,NormTwist.LFunction,Complex.ofReal_neg,neg_mul,sub_neg_eq_add]

theorem brief_coefficient (χ : AngularCharacter) (τ : ℝ)
    (J : Ideal ActualEisensteinCubic.O) (hJ : J≠0) :
    NormTwist.twistedIdealHom χ (-τ) J=
      χ.idealHom J*(J.absNorm:ℂ)^(-(τ:ℂ)*I) := by
  simp only [NormTwist.twistedIdealHom_apply,NormTwist.normTwist_apply,
    if_neg hJ,Complex.ofReal_neg]

theorem briefLFunction_eq_series (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : 1<s.re) : briefLFunction χ τ s=
      IdealEuler.series (NormTwist.twistedIdealHom χ (-τ)) s :=
  NormTwist.LFunction_eq_series χ (-τ) s hs

theorem brief_norm_twist_nonzero (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (7/8:ℝ)<s.re)
    (hpole : χ.k=0 → χ.residue=1 → s≠1-(τ:ℂ)*I) :
    briefLFunction χ τ s≠0 := by
  apply norm_twist_nonzero χ (-τ) s hs
  simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hpole

example : ∀(χ : AngularCharacter)(τ : ℝ)(s : ℂ),
    (7/8:ℝ)<s.re → (χ.k=0 → χ.residue=1 → s≠1-(τ:ℂ)*I) →
    briefLFunction χ τ s≠0 := brief_norm_twist_nonzero

end OAI.SevenEighths.Angular.PhysicalFinalAssembly
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.norm_twist_nonzero
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.briefLFunction_eq_shift
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.brief_coefficient
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.briefLFunction_eq_series
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.brief_norm_twist_nonzero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalFinalAssembly.norm_twist_nonzero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalFinalAssembly.brief_norm_twist_nonzero
