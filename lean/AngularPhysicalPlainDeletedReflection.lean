import AngularPhysicalPlainRestoration

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainDeletion
open CenteredMomentReflectionDeletion (DecayTwo norm norm_pos outside SmoothIdeal OutsideIdeal
  splitEquiv pair_radial_summable_norm normalization_factor subset_product_norm_pos schwartz_decayTwo)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def reflectedTerm (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * η.idealHom (∏ P ∈ D,P) * ηi.idealHom H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P) : ℝ) * norm H.val) : ℂ) *
    Dyadic.polynomial (ηi.excludePrimes S hS) false F
      (Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val)) 0 0

lemma reflectedTerm_eq (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H =
      ((moebius (∏ P ∈ D,P) : ℂ) *
        (η.idealHom (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ))) *
      (ηi.idealHom H.val.val / (Real.sqrt (norm H.val) : ℂ) *
        Dyadic.polynomial (ηi.excludePrimes S hS) false F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val) 0 0) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem deletion_reflection (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hreflect : ∀ Y : ℝ, 0<Y → Dyadic.polynomial η false W Y 0 0 =
      G * Dyadic.polynomial ηi false F (Q/Y) 0 0)
    (X : ℝ) (hX : 0<X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS F X Q D)) ∧
    Dyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm η ηi S hS F X Q D H := by
  have hnorm (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D,P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D,P) : ℂ) *
      (η.idealHom (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq η ηi S hS F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius η S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]


end OAI.SevenEighths.Angular.PlainDeletion

#print axioms OAI.SevenEighths.Angular.PlainDeletion.deletion_reflection
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainDeletion.deletion_reflection
