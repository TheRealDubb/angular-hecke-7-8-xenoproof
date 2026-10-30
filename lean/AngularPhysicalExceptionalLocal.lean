import AngularInducedVolume
import OAI.NumberTheory.DirichletL.CenteredExceptionalProfile

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
open UniqueFactorizationMonoid CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
open CenteredExceptionalCount CenteredMomentCanonical
open CenteredExceptionalProfile (valuation_mod_six_of_unit_agreement)
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem nonzero_on_fixed_units (Q : Ideal O) (hQ : Q≠⊤) (n : O) (hn : n-1∈Q) : n≠0 := by
  intro hz
  have h1 : (1:O)∈Q := by simpa [hz] using Q.neg_mem hn
  exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)

theorem elementCoeff_eq_of_inducedBy (χ ψ : AngularCharacter) (h : InducedBy χ ψ)
    (n : O) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    χ.elementCoeff n=ψ.elementCoeff n := by
  have he := h (Ideal.span {n})
  simpa only [hc,ite_true,χ.idealHom_span,ψ.idealHom_span] using he

theorem elementCoeff_phase_on_units (ψ : AngularCharacter) (Q : Ideal O) (hQ : Q≠⊤)
    (hψ : Q≤ψ.modulus) (n : O) (hn : n-1∈Q) :
    ψ.elementCoeff n=alpha n^ψ.k := by
  rw [ψ.elementCoeff_eq (nonzero_on_fixed_units Q hQ n hn),
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn),map_one,mul_one]

theorem elementCoeff_phase_of_inducedBy (χ ψ : AngularCharacter) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q≠⊤) (hψ : Q≤ψ.modulus)
    (n : O) (hn : n-1∈Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    χ.elementCoeff n=alpha n^ψ.k := by
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hc]
  exact elementCoeff_phase_on_units ψ Q hQ hψ n hn

theorem local_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : AngularCharacter) (htype : ψ₁.k=ψ₂.k)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q K I J P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (hrow₁ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      χ₁.elementCoeff n = η.elementCoeff n * idealRowHom n I)
    (hrow₂ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      χ₂.elementCoeff n = η.elementCoeff n * idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  let L := ((K * η.modulus) * χ₁.modulus) * χ₂.modulus
  have hL : L ≠ 0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero hK η.modulus_ne_bot) χ₁.modulus_ne_bot) χ₂.modulus_ne_bot
  apply valuation_mod_six_of_unit_agreement Q L I J P hL hI hJ hg hchar hQP
  intro n hn hc
  obtain ⟨⟨⟨hcK, hcη⟩, hc₁⟩, hc₂⟩ :=
    (show ((IsCoprime (Ideal.span {n}) K ∧ IsCoprime (Ideal.span {n}) η.modulus) ∧
      IsCoprime (Ideal.span {n}) χ₁.modulus) ∧ IsCoprime (Ideal.span {n}) χ₂.modulus from by
        simpa only [L, IsCoprime.mul_right_iff] using hc)
  have he₁ := elementCoeff_phase_of_inducedBy χ₁ ψ₁ h₁ Q hQ hψ₁ n hn hc₁
  have he₂ := elementCoeff_phase_of_inducedBy χ₂ ψ₂ h₂ Q hQ hψ₂ n hn hc₂
  rw [hrow₁ n hn hcK] at he₁
  rw [hrow₂ n hn hcK] at he₂
  have hn0 := nonzero_on_fixed_units Q hQ n hn
  have hη : η.elementCoeff n ≠ 0 := by
    rw [η.elementCoeff_eq hn0]
    exact mul_ne_zero (zpow_ne_zero _ (alpha_ne_zero hn0))
      (MulChar.apply_ne_zero_iff.mpr ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcη))
  rw [htype] at he₁
  exact mul_left_cancel₀ hη (he₁.trans he₂.symm)

theorem actual_row_on_fixed_units (η χ : AngularCharacter) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, χ.elementCoeff n = rowTwist η.elementHom.toMonoidHom m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    χ.elementCoeff n = η.elementCoeff n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((η.elementCoeff n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem actual_rows_good_profile (η χ₁ χ₂ ψ₁ ψ₂ : AngularCharacter) (htype : ψ₁.k=ψ₂.k)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u₁ u₂ : Oˣ) (a₁ b₁ a₂ b₂ : ℕ) (r₁ r₂ : O)
    (hr₁ : CanonicalQuadraticSieve.Supported (Ideal.span {r₁}))
    (hr₂ : CanonicalQuadraticSieve.Supported (Ideal.span {r₂}))
    (hpr₁ : λ₀ ^ 2 ∣ r₁ - 1) (hpr₂ : λ₀ ^ 2 ∣ r₂ - 1)
    (hx₁ : f ^ 4 * z₁ = (u₁ : O) * λ₀ ^ a₁ * (2 : O) ^ b₁ * r₁)
    (hx₂ : f ^ 4 * z₂ = (u₂ : O) * λ₀ ^ a₂ * (2 : O) ^ b₂ * r₂)
    (hχ₁ : ∀ n, χ₁.elementCoeff n = rowTwist η.elementHom.toMonoidHom m f z₁ n)
    (hχ₂ : ∀ n, χ₂.elementCoeff n = rowTwist η.elementHom.toMonoidHom m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) (hQP : IsCoprime Q P) :
    valuation (Ideal.span {r₁}) P % 6 = valuation (Ideal.span {r₂}) P % 6 := by
  apply local_rows_profile η χ₁ χ₂ ψ₁ ψ₂ htype h₁ h₂ Q (Ideal.span {m})
    (Ideal.span {r₁}) (Ideal.span {r₂}) P hQ (Ideal.span_singleton_eq_bot.not.mpr hm)
    hψ₁ hψ₂ hr₁ hr₂ hg hchar hQP
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₁ m f z₁ hmLam hm2 u₁ a₁ b₁ r₁ hr₁ hpr₁ hx₁ hχ₁ n (hQ72 hn) hc
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₂ m f z₂ hmLam hm2 u₂ a₂ b₂ r₂ hr₂ hpr₂ hx₂ hχ₂ n (hQ72 hn) hc

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.actual_rows_good_profile
