import AngularRawCoefficientGates
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedGeometry

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular
local notation "O" => HeckeFamily.O

theorem AngularCharacter.norm_idealHom_one_of_coprime (χ : AngularCharacter) (J : Ideal O)
    (hJ : J≠⊥) (hc : IsCoprime J χ.modulus) : ‖χ.idealHom J‖=1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  have hg : Submodule.IsPrincipal.generator J≠0 := fun h =>
    hJ ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J).mpr h)
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  rw [←Ideal.span_singleton_generator J,AngularCharacter.idealHom_span,
    AngularCharacter.norm_elementCoeff χ hg]
  obtain ⟨u,hu⟩ := hu
  rw [←hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

theorem AngularCharacter.idealHom_ne_zero_of_coprime (χ : AngularCharacter) (J : Ideal O)
    (hJ : J≠⊥) (hc : IsCoprime J χ.modulus) : χ.idealHom J≠0 := by
  intro hz
  have hn := χ.norm_idealHom_one_of_coprime J hJ hc
  simpa only [hz,norm_zero,zero_ne_one] using hn

theorem AngularCharacter.prime_coprime_of_norm_gt (χ : AngularCharacter) (P : Ideal O)
    (hP : Prime P) (hN : (χ.modulus.absNorm:ℝ)<(P.absNorm:ℝ)) : IsCoprime P χ.modulus :=
  InverseInitialExcludedGeometry.prime_coprime_of_norm_gt hP χ.modulus_ne_bot hN

#print axioms AngularCharacter.norm_idealHom_one_of_coprime
#print axioms AngularCharacter.idealHom_ne_zero_of_coprime
end OAI.SevenEighths.Angular
