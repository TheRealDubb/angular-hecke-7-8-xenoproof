import AngularPlainStripBound
import AngularDeletionBounds
import AngularFamilyConjugation

/-! The reflected bound for the actual source-modulus angular L-function.
Finite Euler factors remain explicit until their proved subpower bounds are
applied. Constants may depend on the fixed nonzero angular order. -/
noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set

namespace OAI.SevenEighths.Angular.PlainReflection
open ActualEisensteinCubic PrimitiveReduction FamilyContinuation HeckeDeletionBounds

theorem primitiveL_eq_family_primitive (χ : AngularCharacter) (hk : χ.k ≠ 0) (s : ℂ) :
    primitiveL χ s = LFunction (primitive χ) s := by
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  exact primitive_eq_family (generator χ) (primitive χ) rfl (primitive_isPrimitive χ) hk s

theorem original_reflected_bound (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ χ : AngularCharacter, χ.k ≠ 0 → χ.k.natAbs = n → ∀ s : ℂ,
    -(1/10 : ℝ) ≤ s.re → s.re ≤ 1/2 →
    ‖LFunction χ s‖ ≤ C*((primitive χ).modulus.absNorm:ℝ)^(1/2-s.re)*(3+|s.im|)^2 *
      ‖LFunction χ (1-conj s)‖ *
      (‖factors χ s‖ * ‖(factors χ (1-conj s))⁻¹‖) := by
  obtain ⟨C,hC,hbound⟩ := primitive_reflected_bound n
  refine ⟨C,hC,?_⟩
  intro χ hk hn s hl hr
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  have h := hbound (generator χ) (primitive χ) rfl (primitive_isPrimitive χ) hk hn s hl hr
  rw [FamilyConjugation.LFunction_conjugate (primitive χ) hk (1-s),norm_conj,
    map_sub,map_one] at h
  change ‖LFunction (primitive χ) s‖ ≤
    C*((primitive χ).modulus.absNorm:ℝ)^(1/2-s.re)*(3+|s.im|)^2 *
      ‖LFunction (primitive χ) (1-conj s)‖ at h
  have hid (z : ℂ) : LFunction χ z = LFunction (primitive χ) z * factors χ z := by
    rw [FamilyContinuation.LFunction,primitiveL_eq_family_primitive χ hk]
  have hd : factors χ (1-conj s) ≠ 0 := factors_ne_zero χ (by simp; linarith)
  have he : LFunction (primitive χ) (1-conj s) =
      LFunction χ (1-conj s) * (factors χ (1-conj s))⁻¹ := by
    rw [hid]
    field_simp
  rw [he,norm_mul] at h
  rw [hid,norm_mul]
  calc
    _ ≤ (C*((primitive χ).modulus.absNorm:ℝ)^(1/2-s.re)*(3+|s.im|)^2 *
        (‖LFunction χ (1-conj s)‖ * ‖(factors χ (1-conj s))⁻¹‖)) *
          ‖factors χ s‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem original_reflected_subpower (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : AngularCharacter,
    χ.k ≠ 0 → χ.k.natAbs = n → ∀ s : ℂ,
    -(1/10 : ℝ) ≤ s.re → s.re ≤ 1/2 →
    ‖LFunction χ s‖ ≤ C*(χ.modulus.absNorm:ℝ)^(1/2-s.re) *
      ((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+2*ε) *
      (3+|s.im|)^2 * ‖LFunction χ (1-conj s)‖ := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_bound n
  obtain ⟨Cl,hCl,hleft⟩ := DeletionBounds.factors_any_re_subpower_bound ε hε
  obtain ⟨Cr,hCr,hright⟩ := DeletionBounds.factors_radical_subpower_bound
    (1/2) ε (by norm_num) hε
  refine ⟨Cg*Cl*Cr,by positivity,?_⟩
  intro χ hk hn s hl hr
  have hR : 0 < ((radical χ.modulus).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hd₁ : ‖factors χ s‖ ≤
      Cl*((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+ε) :=
    hleft χ.modulus (primitive χ) s
  have hd₂ : ‖(factors χ (1-conj s))⁻¹‖ ≤
      Cr*((radical χ.modulus).absNorm:ℝ)^ε := by
    have h := hright χ.modulus (primitive χ) (1-conj s) (by simp; linarith)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hd : ‖factors χ s‖ * ‖(factors χ (1-conj s))⁻¹‖ ≤
      (Cl*Cr)*((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+2*ε) := by
    calc
      _ ≤ (Cl*((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+ε)) *
          (Cr*((radical χ.modulus).absNorm:ℝ)^ε) :=
        mul_le_mul hd₁ hd₂ (norm_nonneg _) (mul_nonneg hCl.le (Real.rpow_nonneg hR.le _))
      _ = _ := by
        have he : ((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+ε) *
            ((radical χ.modulus).absNorm:ℝ)^ε =
            ((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+2*ε) := by
          rw [←Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (Cl*Cr)*(((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+ε) *
              ((radical χ.modulus).absNorm:ℝ)^ε) := by ring
          _ = _ := by rw [he]
  have hQ : ((primitive χ).modulus.absNorm:ℝ)^(1/2-s.re) ≤
      (χ.modulus.absNorm:ℝ)^(1/2-s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast PrimitiveReduction.norm_le χ) (by linarith)
  calc
    _ ≤ Cg*((primitive χ).modulus.absNorm:ℝ)^(1/2-s.re)*(3+|s.im|)^2 *
        ‖LFunction χ (1-conj s)‖ *
        (‖factors χ s‖ * ‖(factors χ (1-conj s))⁻¹‖) := hreflect χ hk hn s hl hr
    _ ≤ Cg*(χ.modulus.absNorm:ℝ)^(1/2-s.re)*(3+|s.im|)^2 *
        ‖LFunction χ (1-conj s)‖ *
        ((Cl*Cr)*((radical χ.modulus).absNorm:ℝ)^(max (-s.re) 0+2*ε)) := by
      apply mul_le_mul _ hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end OAI.SevenEighths.Angular.PlainReflection
