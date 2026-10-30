import AngularPhysicalExceptionalForcing

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

def FixedInducingRow (η : AngularCharacter) (Q : Ideal O) (m A z : O) : Prop :=
  ∃ χ ψ : AngularCharacter, χ.k=η.k ∧ ψ.k=η.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
    InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
    ∀ n, χ.elementCoeff n = rowTwist η.elementHom.toMonoidHom m 1 (A * z) n

theorem fixed_inducing_rows_profile (η : AngularCharacter) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨χ₁, ψ₁, _, hk₁, _, hi₁, hψ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, ψ₂, _, hk₂, _, hi₂, hψ₂, hχ₂⟩ := h₂
  have he := actual_rows_profile η χ₁ χ₂ ψ₁ ψ₂ (hk₁.trans hk₂.symm) hi₁ hi₂ Q hQ hQ72 hψ₁ hψ₂
    m 1 (A * z₁) (A * z₂) hm one_ne_zero (mul_ne_zero hA hz₁) (mul_ne_zero hA hz₂)
    hmLam hm2 hχ₁ hχ₂ P hg h2 hQP
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at he
  exact valuation_mod_six_cancel_frozen _ _ _ P (Ideal.span_singleton_eq_bot.not.mpr hA)
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) he

theorem fixed_inducing_rows_same_remainder (η : AngularCharacter) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (hsector : ∀ P ∈ S, valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6) :
    sixthRemainder (Ideal.span {z₁}) = sixthRemainder (Ideal.span {z₂}) := by
  apply sixthRemainder_eq_of_prime_profile (sixthRemainder_ne_zero _)
  intro P hP
  rw [sixthRemainder_valuation]
  by_cases hPS : P ∈ S
  · exact hsector P hPS
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨hg, h2, hQP⟩ := houtside P hP hPS
    exact fixed_inducing_rows_profile η Q hQ hQ72 m A z₁ z₂ hm hA hz₁ hz₂ hmLam hm2
      h₁ h₂ P hg h2 hQP

theorem fixed_inducing_remainder_card (η : AngularCharacter) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z) :
    (T.image (fun z => sixthRemainder (Ideal.span {z}))).card ≤ 6 ^ S.card := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  let code : Ideal O → (S → Fin 6) :=
    fun R P => ⟨valuation R P.val % 6, Nat.mod_lt _ (by decide)⟩
  have hinj : (Rs : Set (Ideal O)).InjOn code := by
    intro R hR R' hR' he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hR'
    apply fixed_inducing_rows_same_remainder η Q hQ hQ72 m A z z' hm hA (hT z hz) (hT z' hz')
      hmLam hm2 (hex z hz) (hex z' hz') S houtside
    intro P hP
    have hh := congrArg (fun f : S → Fin 6 => (f ⟨P, hP⟩).val) he
    simpa only [code, sixthRemainder_valuation, Nat.mod_mod] using hh
  have hc := Finset.card_le_card_of_injOn code (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Rs] using hc

theorem fixed_inducing_row_count (η : AngularCharacter) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ S.card * C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  have hRs : ∀ R ∈ Rs, R ≠ 0 := by
    intro R hR
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hR
    exact sixthRemainder_ne_zero _
  have hRnorm : ∀ R ∈ Rs, Z ^ (2 * F) ≤ (Ideal.absNorm R : ℝ) := by
    intro R hR
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨χ, ψ, _, hk, _, hi, hψ, hχ⟩ := hex z hz
    have hf := (actual_forced_fourth_power η χ ψ hk hi Q hQ hQ72 hψ m A z hm hA
      (hT z hz) hmLam hm2 hχ D hD hgood).2
    calc
      Z ^ (2 * F) = (Z ^ (F / 2)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1
        norm_num
        ring
      _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) hDnorm _
      _ ≤ _ := hf
  have hcount := element_count_power_scale_family T Rs hRs Z C M (2 * F) hZ hC hRnorm hT
    (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩) hN
  have hcard : (Rs.card : ℝ) ≤ (6 : ℝ) ^ S.card := by
    exact_mod_cast fixed_inducing_remainder_card η Q hQ hQ72 m A hm hA hmLam hm2 S houtside T hT hex
  apply hcount.trans
  gcongr

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixed_inducing_row_count
