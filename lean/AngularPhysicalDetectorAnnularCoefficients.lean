import AngularPhysicalCommonMaskSlots
import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular

noncomputable section
open Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorMovingHoles
open HeckePrimeAnnular HeckeDyadic CenteredMomentCommonMaskEnergy
local notation "O" => ActualEisensteinCubic.O
theorem annular_coefficient_bounds (W : ℝ → ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : Continuous W) :
    ∃ B : ℝ, 0 < B ∧ ∀ (ν : AngularCharacter) (P σ v t : ℝ), 0<P → lo≤σ → σ≤hi →
      ∀ I : Ideal O, I≠0 →
      ‖heightCoefficient (fun I=>ν.idealHom I*annularWeight W P σ v I) t I‖ ≤ B := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  apply (show ‖ν.idealHom I*annularWeight W P σ v I‖ ≤ ‖annularWeight W P σ v I‖ by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ν.norm_idealHom_le_one I)).trans
  by_cases hz : W ((I.absNorm : ℝ)/P)=0
  · simp [annularWeight,hz,hB.le]
  · have hs := hWs hz
    rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
    simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs


end OAI.SevenEighths.Angular.PhysicalDetectorMovingHoles

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorMovingHoles.annular_coefficient_bounds
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorMovingHoles.annular_coefficient_bounds
