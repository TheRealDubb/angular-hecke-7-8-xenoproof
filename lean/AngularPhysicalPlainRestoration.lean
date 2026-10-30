import AngularPhysicalPlainRestorationSplit

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainDeletion
open CenteredMomentReflectionDeletion (DecayTwo norm norm_pos outside SmoothIdeal OutsideIdeal
  splitEquiv pair_radial_summable_norm normalization_factor subset_product_norm_pos schwartz_decayTwo)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma normalized_restoration_term (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (hX : 0<X) (D : SmoothIdeal S) :
    η.idealHom D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      Dyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (η.idealHom D.val.val *
      ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / (X / norm D.val))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D.val))]
  change η.idealHom D.val.val / (Real.sqrt (norm D.val) : ℂ) *
    ((Real.sqrt (X / norm D.val) : ℂ)⁻¹ *
    ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / (X / norm D.val))) = _
  have h := normalization_factor X (norm D.val) hX (norm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (η.idealHom D.val.val *
    ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / (X / norm D.val))) * h

theorem normalized_restoration (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => η.idealHom D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      Dyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0) ∧
    Dyadic.polynomial η false F X 0 0 =
      ∑' D : SmoothIdeal S, η.idealHom D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        Dyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 := by
  constructor
  · apply ((restoration_plain_summable η S hS F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm
  · rw [polynomial_plain _ _ _ hX]
    change (Real.sqrt X : ℂ)⁻¹ * (∑' I : NI, η.idealHom I.val * F (norm I / X)) = _
    rw [restoration_plain η S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm


end OAI.SevenEighths.Angular.PlainDeletion

#print axioms OAI.SevenEighths.Angular.PlainDeletion.normalized_restoration
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainDeletion.normalized_restoration
