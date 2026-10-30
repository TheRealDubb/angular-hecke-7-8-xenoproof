import AngularPhysicalExceptionalLocal

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
open UniqueFactorizationMonoid CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
open CenteredExceptionalCount CenteredMomentCanonical
open CenteredExceptionalProfile (valuation_mod_six_of_unit_agreement valuation_supported_numerator
  valuation_mod_six_cancel_frozen)
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem actual_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : AngularCharacter) (htype : ψ₁.k=ψ₂.k)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ₁ : ∀ n, χ₁.elementCoeff n = rowTwist η.elementHom.toMonoidHom m f z₁ n)
    (hχ₂ : ∀ n, χ₂.elementCoeff n = rowTwist η.elementHom.toMonoidHom m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨u₁, a₁, b₁, r₁, hr₁, hpr₁, hx₁⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₁) (mul_ne_zero (pow_ne_zero _ hf) hz₁)
  obtain ⟨u₂, a₂, b₂, r₂, hr₂, hpr₂, hx₂⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₂) (mul_ne_zero (pow_ne_zero _ hf) hz₂)
  have hr₁0 := Ideal.span_singleton_eq_bot.not.mp hr₁.1
  have hr₂0 := Ideal.span_singleton_eq_bot.not.mp hr₂.1
  have h := actual_rows_good_profile η χ₁ χ₂ ψ₁ ψ₂ htype h₁ h₂ Q hQ hQ72 hψ₁ hψ₂
    m f z₁ z₂ hm hmLam hm2 u₁ u₂ a₁ b₁ a₂ b₂ r₁ r₂ hr₁ hr₂ hpr₁ hpr₂ hx₁ hx₂
    hχ₁ hχ₂ P hg (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP
  rw [← valuation_supported_numerator _ u₁ a₁ b₁ r₁ hr₁0 hx₁ P hg h2,
    ← valuation_supported_numerator _ u₂ a₂ b₂ r₂ hr₂0 hx₂ P hg h2,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at h
  exact valuation_mod_six_cancel_frozen _ _ _ P
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hf))
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) h

theorem local_row_valuation_zero (η χ ψ : AngularCharacter) (htype : ψ.k=η.k) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      χ.elementCoeff n = η.elementCoeff n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hn0 := nonzero_on_fixed_units Q hQ n hnQ
  have hη : η.elementCoeff n=alpha n^η.k := by
    rw [η.elementCoeff_eq hn0,
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn),map_one,mul_one]
  have he := elementCoeff_phase_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK,hη,htype] at he
  have hp : alpha n^η.k≠0 := zpow_ne_zero _ (alpha_ne_zero hn0)
  have hh : idealRowHom n I=1 := mul_left_cancel₀ hp (he.trans (mul_one _).symm)
  simpa only [map_one] using hh

theorem actual_row_numerator_valuation_zero (η χ ψ : AngularCharacter) (htype : ψ.k=η.k) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, χ.elementCoeff n = rowTwist η.elementHom.toMonoidHom m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ htype h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem actual_row_forced_residue_four (η χ ψ : AngularCharacter) (htype : ψ.k=η.k) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, χ.elementCoeff n = rowTwist η.elementHom.toMonoidHom m 1 (A * z) n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hA2 : valuation (Ideal.span {A}) P % 6 = 2) :
    valuation (Ideal.span {z}) P % 6 = 4 := by
  have he := actual_row_numerator_valuation_zero η χ ψ htype h Q hQ hQ72 hψ m 1 (A * z)
    hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2 hχ P hg h2 hQP hηP
  simp only [one_pow, one_mul] at he
  rw [← Ideal.span_singleton_mul_span_singleton, valuation_mul _ _ _
    (Ideal.span_singleton_eq_bot.not.mpr hA) (Ideal.span_singleton_eq_bot.not.mpr hz),
    Nat.add_mod, hA2] at he
  omega

theorem actual_forced_fourth_power (η χ ψ : AngularCharacter) (htype : ψ.k=η.k) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, χ.elementCoeff n = rowTwist η.elementHom.toMonoidHom m 1 (A * z) n)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2) :
    D ^ 4 ∣ sixthRemainder (Ideal.span {z}) ∧
      (Ideal.absNorm D : ℝ) ^ 4 ≤ Ideal.absNorm (sixthRemainder (Ideal.span {z})) := by
  have hf : ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4 := by
    intro P hP
    have hp := prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    obtain ⟨hg, h2, hQP, hηP, hA2⟩ := hgood P hP
    exact actual_row_forced_residue_four η χ ψ htype h Q hQ hQ72 hψ m A z hm hA hz hmLam hm2 hχ
      P hg h2 hQP hηP hA2
  exact ⟨forced_fourth_power_dvd _ D hD hf, forced_fourth_power_norm_le _ D hD hf⟩

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.actual_forced_fourth_power
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.actual_forced_fourth_power
