import AngularPrimaryVolume

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PrimaryVolume
open CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)
open AnnularSchwartz PlaneVolume
local notation "O" => ActualEisensteinCubic.O

theorem masked_hecke_volume
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    (ψ : AngularCharacter) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (a b : ℝ) (ha : 0<a) (X : ℝ) (hX : 0<X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryCoefficient ψ
    let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperFourier (annularCLM ψ.k a b ha W) 0)
    ‖(∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * (nonzeroLatticeEnvelopeConstant*fourierControl (annularCLM ψ.k a b ha W))) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryCoefficient ψ
  let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
    ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperFourier (annularCLM ψ.k a b ha W) 0)
  let B := (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * (nonzeroLatticeEnvelopeConstant*fourierControl (annularCLM ψ.k a b ha W))
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg nonzeroLatticeEnvelopeConstant_nonneg (fourierControl_nonneg _))
  have hnD (D : Ideal O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := fixed_period_volume c hc h3 ψ hmod W a b ha hs
      (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryCoefficient_norm ψ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX (fun x hx=>(hs hx).2)]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end OAI.SevenEighths.Angular.PrimaryVolume
