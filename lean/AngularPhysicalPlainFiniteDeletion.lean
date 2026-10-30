import AngularPhysicalPlainOutside

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainDeletion
open CenteredMomentReflectionDeletion (DecayTwo norm norm_pos outside outside_iff_coprime
  radial_summable_norm outside_mul_prime subset_product_nonzero subset_product_norm_pos
  normalization_factor subset_product_moebius schwartz_decayTwo)
open CenteredMomentComparisonReflection (inverse_half_power)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem finite_deletion_plain (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η S F X = ∑ D ∈ S.powerset, (-1 : ℂ)^D.card * η.idealHom (∏ P ∈ D, P) *
      (∑' I : NI, η.idealHom I.val * F (norm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty => simp [outsideSum, outside]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert η S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, map_mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (η : AngularCharacter) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (D : NI) :
    η.idealHom D.val / (Real.sqrt (norm D) : ℂ) *
      Dyadic.polynomial η false F (X / norm D) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (η.idealHom D.val *
      ∑' I : NI, η.idealHom I.val * F (norm I / (X / norm D))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D))]
  change η.idealHom D.val / (Real.sqrt (norm D) : ℂ) *
    ((Real.sqrt (X / norm D) : ℂ)⁻¹ *
      ∑' I : NI, η.idealHom I.val * F (norm I / (X / norm D))) = _
  have h := normalization_factor X (norm D) hX (norm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (η.idealHom D.val *
    ∑' I : NI, η.idealHom I.val * F (norm I / (X / norm D))) * h

theorem normalized_finite_deletion (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Dyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (-1 : ℂ)^D.card *
        (η.idealHom (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        Dyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [polynomial_plain _ _ _ hX]
  have he : (∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F ((I.val.absNorm : ℝ) / X)) =
      outsideSum η S F X := by
    apply tsum_congr
    intro I
    rw [deleted_coefficient]
    rfl
  rw [he, finite_deletion_plain η S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term η F X hX ⟨∏P∈D,P, subset_product_nonzero D hDS⟩
  dsimp only [CenteredMomentReflectionDeletion.norm] at ht
  dsimp only [CenteredMomentReflectionDeletion.norm]
  linear_combination -(-1 : ℂ)^D.card * ht

theorem normalized_finite_deletion_moebius (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Dyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D,P) : ℂ) *
        (η.idealHom (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        Dyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [normalized_finite_deletion η S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]


end OAI.SevenEighths.Angular.PlainDeletion

#print axioms OAI.SevenEighths.Angular.PlainDeletion.normalized_finite_deletion_moebius
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainDeletion.normalized_finite_deletion_moebius
