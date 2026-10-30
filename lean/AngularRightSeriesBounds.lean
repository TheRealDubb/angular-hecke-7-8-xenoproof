import AngularFamilyContinuation
import OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PlainReflection
open ActualEisensteinCubic FamilyContinuation

theorem LFunction_norm_le (χ : AngularCharacter) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction χ s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series χ s hs1,AngularCharacter.series,IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm χ.idealHom χ.norm_idealHom_le_one s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ))
  intro I
  change ‖χ.idealHom I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_idealHom_le_one I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

theorem inverse_LFunction_norm_le (χ : AngularCharacter) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖(LFunction χ s)⁻¹‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series χ s hs1,AngularCharacter.series,
    ←IdealEuler.inverseSeries_eq_inv χ.idealHom χ.norm_idealHom_le_one s hs1]
  have hsum := IdealEuler.inverse_summable_norm χ.idealHom χ.norm_idealHom_le_one s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I:ℂ) *
    (χ.idealHom I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_idealHom_le_one I)
    _ ≤ _ := HeckeReciprocalBound.normWeight_le_of_re_ge hs I

end OAI.SevenEighths.Angular.PlainReflection
