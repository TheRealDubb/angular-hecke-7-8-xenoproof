import AngularMaskedVolume
import AngularPrimitiveReduction
import AngularInverseRows

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PrimaryVolume
open CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open AnnularSchwartz PlaneVolume
open CenteredMomentHeckeVolume (fixedPeriod fixedPeriod_ne_zero fixedPeriod_three span_fixedPeriod_le)
local notation "O" => ActualEisensteinCubic.O

def InducedBy (χ ψ : AngularCharacter) : Prop :=
  ∀ I : Ideal O, χ.idealHom I = if IsCoprime I χ.modulus then ψ.idealHom I else 0

theorem exists_primitive_inducedBy (χ : AngularCharacter) :
    ∃ ψ : AngularCharacter, ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      χ.modulus ≤ ψ.modulus ∧ InducedBy χ ψ := by
  exact ⟨PrimitiveReduction.primitive χ,rfl,PrimitiveReduction.primitive_isPrimitive χ,
    PrimitiveReduction.modulus_le χ,PrimitiveReduction.idealHom_source_mask χ⟩

theorem induced_primaryCoefficient (χ ψ : AngularCharacter)
    (hind : InducedBy χ ψ) (I : Ideal O) :
    primaryCoefficient χ I =
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I := by
  change (if primaryGenerator I=0 then 0 else χ.idealHom I)=
    (if IsCoprime I χ.modulus then (1:ℂ) else 0)*(if primaryGenerator I=0 then 0 else ψ.idealHom I)
  rw [hind I]
  split_ifs <;> simp only [one_mul,zero_mul]

theorem primaryCoefficient_actual_row (η χ : AngularCharacter) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, χ.elementCoeff n=CanonicalRowCompletion.rowTwist
      η.elementHom.toMonoidHom m 1 (A₀*z) n) (I : Ideal O) :
    primaryCoefficient χ I=χ.idealHom I := by
  change (if primaryGenerator I=0 then 0 else χ.idealHom I)=_
  by_cases hI : I=0
  · simp only [hI,primaryGenerator_zero,map_zero,ite_self]
  by_cases hg : primaryGenerator I=0
  · rw [ite_eq_left hg]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
    have hbad : ¬Supported (Ideal.span {n}) := by
      intro h
      have hp : primaryGenerator (Ideal.span {n}) ≠ 0 :=
        PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n |>.mpr ((CanonicalQuadraticSieve.supported_span_iff n).mp h).1
      exact hp (hs ▸ hg)
    rw [← hs,χ.idealHom_span,hrow,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hbad]
  · rw [ite_eq_right hg]

def density (c : O) (hc : c ≠ 0) (ψ : AngularCharacter) (R : Ideal O) : ℂ :=
  letI := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)) *
    (1/(‖eisEmbedding c‖^2:ℂ))*(∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)

theorem density_norm_le (c : O) (hc : c ≠ 0) (ψ : AngularCharacter) (R : Ideal O) (hR : R ≠ 0) :
    ‖density c hc ψ R‖ ≤
      ((idealDivisors R).card:ℝ)*(Nat.card (O ⧸ Ideal.span {c}):ℝ)/‖eisEmbedding c‖^2 := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hdiv : ‖∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ ≤
      ((idealDivisors R).card:ℝ) := by
    calc
      _ ≤ ∑ D ∈ idealDivisors R, ‖(moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _D ∈ idealDivisors R, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
        have hN : (1:ℝ) ≤ Ideal.absNorm D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
        rw [norm_div,norm_mul,Complex.norm_natCast]
        apply (div_le_one (by linarith : 0 < (Ideal.absNorm D:ℝ))).mpr
        exact ((mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one D)).trans
          (primaryCoefficient_norm ψ D)).trans hN
      _ = _ := by simp
  have hres : ‖∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r‖ ≤
      (Nat.card (O ⧸ Ideal.span {c}):ℝ) := by
    calc
      _ ≤ ∑ r : O ⧸ Ideal.span {c}, ‖periodicValue c ψ r‖ := norm_sum_le _ _
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  unfold density
  rw [norm_mul,norm_mul,norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (((idealDivisors R).card:ℝ)*(1/‖eisEmbedding c‖^2))*(Nat.card (O ⧸ Ideal.span {c}):ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdiv (by positivity)) hres (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_induced_volume (η χ ψ : AngularCharacter) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, χ.elementCoeff n=CanonicalRowCompletion.rowTwist
      η.elementHom.toMonoidHom m 1 (A₀*z) n)
    (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (X : ℝ) (hX : 0<X)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) :
    ‖(∑' I : Ideal O, χ.idealHom I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X:ℂ)*(density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperFourier (annularCLM ψ.k a b ha W) 0)‖ ≤
      ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*(nonzeroLatticeEnvelopeConstant*fourierControl (annularCLM ψ.k a b ha W)) := by
  let := finite_quotient_span (fixedPeriod_ne_zero Q hQ)
  let : Fintype (O ⧸ Ideal.span {fixedPeriod Q}) := Fintype.ofFinite _
  have h := masked_hecke_volume (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ)
    (fixedPeriod_three Q) ψ ((span_fixedPeriod_le Q).trans hQψ)
    χ.modulus χ.modulus_ne_bot W a b ha X hX hs
  have he (I : Ideal O) :
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I=χ.idealHom I := by
    rw [← induced_primaryCoefficient χ ψ hind I,primaryCoefficient_actual_row η χ m A₀ z hmLam hm2 hrow I]
  simp_rw [show ∀ I : Ideal O, (if IsCoprime I χ.modulus then (1:ℂ) else 0)*
      (primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) =
        χ.idealHom I*W ((Ideal.absNorm I:ℝ)/X) by intro I; rw [← mul_assoc,he]] at h
  convert h using 1
  · congr 1
    unfold density
    ring
  · rw [Nat.card_eq_fintype_card]
    ring

end OAI.SevenEighths.Angular.PrimaryVolume
