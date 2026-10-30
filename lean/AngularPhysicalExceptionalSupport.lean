import AngularPhysicalExceptionalCount

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
open UniqueFactorizationMonoid CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
open CenteredExceptionalCount CenteredMomentCanonical
open CenteredExceptionalProfile (valuation_mod_six_cancel_frozen outside_fixed_support)
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem fixed_support_exceptional_count (η : AngularCharacter) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) :=
  fixed_inducing_row_count η Q hQ hQ72 m A hm hA hmLam hm2
    (normalizedFactors Q).toFinset (outside_fixed_support Q hQ0 hQ72) T hT hex
    D hD hgood Z C M F hZ hC hDnorm hN

theorem fixed_support_exceptional_count_weaker (η : AngularCharacter) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - F) / 6) := by
  apply (fixed_support_exceptional_count η Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex
    D hD hgood Z C M F (zero_lt_one.trans_le hZ) hC hDnorm hN).trans
  gcongr
  linarith

theorem fixed_inducing_rows_empty (η : AngularCharacter) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (H : ℝ) (hH : H < (Ideal.absNorm D : ℝ) ^ 4)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨χ, ψ, _, hk, _, hi, hψ, hχ⟩ := hex z hz
  have hf := (actual_forced_fourth_power η χ ψ hk hi Q hQ hQ72 hψ m A z hm hA
    (hT z hz) hmLam hm2 hχ D hD hgood).2
  have hr := sixthRemainder_norm_le (Ideal.span {z}) (Ideal.span_singleton_eq_bot.not.mpr (hT z hz))
  exact (not_le_of_gt hH) (hf.trans (hr.trans (hN z hz)))

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixed_support_exceptional_count
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.fixed_support_exceptional_count
