import AngularPhysicalNaturalCharacter

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalDetectorJoint
open NaturalRows
open ConcretePrimeRowBridge (idealGenerator idealGenerator_ne_zero span_idealGenerator)
local notation "O" => ActualEisensteinCubic.O

/-- Principal type-zero characters are determined by their actual ideal
coefficients, even when the presentation moduli are different. -/
theorem type_zero_principal_of_coefficients (χ ψ : AngularCharacter)
    (hkχ : χ.k=0) (hkψ : ψ.k=0)
    (hc : ∀I : Ideal O,χ.idealHom I=ψ.idealHom I) (hp : ψ.residue=1) : χ.residue=1 := by
  apply MulChar.ext
  intro x
  rw [MulChar.one_apply_coe]
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective (x : O⧸χ.modulus)
  obtain ⟨z,hz,hzq⟩ : ∃z : O,z≠0 ∧ Ideal.Quotient.mk χ.modulus z=(x : O⧸χ.modulus) := by
    by_cases h0 : a=0
    · refine ⟨idealGenerator χ.modulus,idealGenerator_ne_zero _ χ.modulus_ne_bot,?_⟩
      have hg : idealGenerator χ.modulus∈χ.modulus := by
        have hg₀ : idealGenerator χ.modulus∈Ideal.span {idealGenerator χ.modulus} :=
          Ideal.subset_span (Set.mem_singleton _)
        exact (congrArg (fun J : Ideal O=>idealGenerator χ.modulus∈J)
          (span_idealGenerator χ.modulus)).mp hg₀
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      simpa only [h0,map_zero] using ha
    · exact ⟨a,h0,ha⟩
  have he : χ.residue x=ψ.residue (Ideal.Quotient.mk ψ.modulus z) := by
    have he := hc (Ideal.span {z})
    rw [AngularCharacter.idealHom_span,AngularCharacter.idealHom_span,
      AngularCharacter.elementCoeff_eq χ hz,AngularCharacter.elementCoeff_eq ψ hz,
      hkχ,hkψ,zpow_zero,one_mul,one_mul,hzq] at he
    exact he
  have hn : χ.residue x≠0 := MulChar.apply_ne_zero_iff.mpr x.isUnit
  have hu : IsUnit (Ideal.Quotient.mk ψ.modulus z) :=
    MulChar.apply_ne_zero_iff.mp (by rw [←he];exact hn)
  rw [he,hp,MulChar.one_apply hu]

theorem nonprincipal_of_coefficients (χ ψ : AngularCharacter) (hk : χ.k=ψ.k)
    (hc : ∀I : Ideal O,χ.idealHom I=ψ.idealHom I)
    (hn : χ.k≠0 ∨ χ.residue≠1) : ψ.k≠0 ∨ ψ.residue≠1 := by
  by_cases hψ : ψ.k=0
  · right
    intro hp
    have hχ := hk.trans hψ
    have hh := type_zero_principal_of_coefficients χ ψ hχ hψ hc hp
    rcases hn with hn|hn
    · exact hn hχ
    · exact hn hh
  · exact Or.inl hψ


end OAI.SevenEighths.Angular.PhysicalDetectorJoint

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.type_zero_principal_of_coefficients
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.type_zero_principal_of_coefficients

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.nonprincipal_of_coefficients
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.nonprincipal_of_coefficients
