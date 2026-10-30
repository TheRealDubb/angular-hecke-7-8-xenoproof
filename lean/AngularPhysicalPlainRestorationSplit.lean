import AngularPhysicalPlainFiniteDeletion

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainDeletion
open CenteredMomentReflectionDeletion (DecayTwo norm norm_pos outside SmoothIdeal OutsideIdeal
  splitEquiv pair_radial_summable_norm normalization_factor subset_product_norm_pos schwartz_decayTwo)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma restricted_pair_summable (η : AngularCharacter) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      η.idealHom (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val,p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (η.norm_idealHom_le_one _)

lemma outside_plain_tsum (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, η.idealHom I.val.val * F (norm I.val / X)) =
      ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / X) := by
  have he := tsum_subtype {I : NI | outside S I.val}
    (fun I : NI => η.idealHom I.val * F (norm I / X))
  change (∑' I : OutsideIdeal S, η.idealHom I.val.val * F (norm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  rw [deleted_coefficient]
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, η.idealHom (D.val.val * J.val.val) *
      F (norm D.val * norm J.val / X)) =
    η.idealHom D.val.val *
      ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / (X / norm D.val)) := by
  rw [← outside_plain_tsum η S hS F, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [map_mul, mul_assoc]
  congr 2
  field_simp

lemma restoration_plain_summable (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => η.idealHom D.val.val *
      ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / (X / norm D.val))) := by
  exact (restricted_pair_summable η S F hF X hX).prod.congr
    (fun D => restoration_inner η S hS F X D)

theorem restoration_plain (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI, η.idealHom I.val * F (norm I / X)) =
      ∑' D : SmoothIdeal S, η.idealHom D.val.val *
        ∑' I : NI, (η.excludePrimes S hS).idealHom I.val * F (norm I / (X / norm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI => η.idealHom I.val * F (norm I / X))
  have hp := (restricted_pair_summable η S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      norm ((splitEquiv S hS).symm p) = norm p.1.val * norm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    η.idealHom (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner η S hS F X D)


end OAI.SevenEighths.Angular.PlainDeletion

#print axioms OAI.SevenEighths.Angular.PlainDeletion.restoration_plain
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainDeletion.restoration_plain
