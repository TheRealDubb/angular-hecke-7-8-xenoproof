import AngularPlainUniformStrip
import AngularTypeZeroEntire
import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedControl
import OAI.NumberTheory.DirichletL.Hecke.DyadicScale

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular
open FamilyContinuation FiniteIdentification HeckeDeletionBounds

theorem PlainReflection.nonprincipal_upper_strip (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : AngularCharacter, (χ.k ≠ 0 ∨ χ.residue ≠ 1) →
      χ.k.natAbs = n → ∀ s : ℂ, -(1/10 : ℝ) ≤ s.re →
      ‖LFunction χ s‖ ≤ C*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
        ((radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨C0, hC0, h0⟩ := HeckeDyadic.original_upper_strip ε hε
  obtain ⟨Cn, hCn, hn⟩ := PlainReflection.original_upper_strip n ε hε
  refine ⟨C0+Cn, by positivity, ?_⟩
  intro χ hχ horder s hs
  by_cases hk : χ.k = 0
  · have hr : χ.residue ≠ 1 := hχ.resolve_left (not_not.mpr hk)
    rw [TypeZeroEntire.LFunction_eq_finite χ hk hr s]
    apply (h0 (toFinite χ hk) hr s hs).trans
    change C0*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
      ((radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 ≤ _
    gcongr
    linarith
  · apply (hn χ hk horder s hs).trans
    gcongr
    linarith

theorem Dyadic.radical_norm_le_modulus (χ : AngularCharacter) :
    ((radical χ.modulus).absNorm : ℝ) ≤ χ.modulus.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
    (map_dvd Ideal.absNorm (HeckeDyadic.radical_dvd χ.modulus χ.modulus_ne_bot))

#print axioms PlainReflection.nonprincipal_upper_strip
end OAI.SevenEighths.Angular
