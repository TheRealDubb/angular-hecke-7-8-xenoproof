import AngularPrimitiveReduction
import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

/-! Finite Euler-product estimates retain the actual angular ideal coefficient.
Only the generic prime-support and local norm inequalities are imported. -/
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.DeletionBounds
open ActualEisensteinCubic HeckeDeletionBounds

def deletedFactors (M : Ideal O) (ψ : AngularCharacter) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => ψ.idealHom P.val)

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : AngularCharacter) {s : ℂ} (hs : σ ≤ s.re) :
    ‖deletedFactors M ψ s‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card ∧
    ‖(deletedFactors M ψ s)⁻¹‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
  have hfactor (P : SmoothMobiusCorrection.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (ψ.idealHom P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (ψ.idealHom P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
      (ψ.norm_idealHom_le_one P.val) hs
  have he : (∏ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ) =
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
    rw [SmoothMobiusCorrection.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold deletedFactors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold deletedFactors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : AngularCharacter) (s : ℂ),
      σ ≤ s.re → ‖deletedFactors M ψ s‖ +
        ‖(deletedFactors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith


theorem factors_radical (M : Ideal O) (ψ : AngularCharacter) (s : ℂ) :
    deletedFactors (radical M) ψ s = deletedFactors M ψ s := by
  unfold deletedFactors radical
  rw [SmoothMobiusCorrection.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : AngularCharacter) (s : ℂ),
      σ ≤ s.re → ‖deletedFactors M ψ s‖ +
        ‖(deletedFactors M ψ s)⁻¹‖ ≤ C*((radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (radical M) (radical_ne_zero M) ψ s hs


theorem factors_bound_any_re (M : Ideal O) (ψ : AngularCharacter) (s : ℂ) :
    ‖deletedFactors M ψ s‖ ≤
      (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card *
        ((radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold deletedFactors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ SmoothMobiusCorrection.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (ψ.norm_idealHom_le_one P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]


theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : AngularCharacter) (s : ℂ),
      ‖deletedFactors M ψ s‖ ≤
        C*((radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card ≤ C*((radical M).absNorm : ℝ)^ε := by
    have h := hb (radical M) (radical_ne_zero M)
    rw [← primeSet_card, radical, SmoothMobiusCorrection.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((radical M).absNorm : ℝ)^ε)*((radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring


end OAI.SevenEighths.Angular.DeletionBounds
