import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
import AngularPhysicalNaturalRelativeSlot
import OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.RelativeFloor
open RelativePrime PlainRows NaturalRows ExceptionalRows CommonMask Dyadic
open QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentCommonMaskEnergy (heightCoefficient heightCoefficient_norm)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentNaturalRowSource (support_prime fixedConductorFactor)
open CenteredMomentAllocatedNaturalSource (primeSupport_product_radical)
local notation "O" => ActualEisensteinCubic.O
open HeckePrimeAnnular
open HeckeDyadic (shift_re)
theorem slot_coefficient_bounds (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B : ℝ,0<B ∧ ∀(ν : AngularCharacter)(P σ v t : ℝ),0<P → lo≤σ → σ≤hi →
    ∀I : Ideal O,I≠0 →
      ‖heightCoefficient (fun I=>ν.idealHom I*annularWeight W P σ v I) t I‖≤B ∧
      (heightCoefficient (fun I=>ν.idealHom I*annularWeight W P σ v I) t I≠0 →
        (I.absNorm:ℝ)≤b*P) := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  constructor
  · apply (show ‖ν.idealHom I*annularWeight W P σ v I‖≤‖annularWeight W P σ v I‖ by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (ν.norm_idealHom_le_one I)).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,HeckeDyadic.shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs
  · intro hn
    have hw : W ((I.absNorm:ℝ)/P)≠0 := by
      intro hh
      exact hn (by simp [heightCoefficient,annularWeight,hh])
    exact (div_le_iff₀ hP).mp (hWs hw).2

end OAI.SevenEighths.Angular.RelativeFloor

#print axioms OAI.SevenEighths.Angular.RelativeFloor.slot_coefficient_bounds
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativeFloor.slot_coefficient_bounds
