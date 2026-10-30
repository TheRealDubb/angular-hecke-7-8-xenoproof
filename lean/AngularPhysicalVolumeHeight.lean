import AngularPhysicalTwistedVolume
import OAI.NumberTheory.DirichletL.Moments.HeckeHeight

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.TwistedVolume
open PrimaryVolume PlainRows AnnularSchwartz PlaneVolume
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight
open EisensteinSchwartzPoisson IdealMobiusDivisorSum
open CenteredMomentHeckeVolume (fixedPeriod fixedPeriod_ne_zero)
local notation "O" => ActualEisensteinCubic.O

theorem volumeControl_polynomial_height (k : ℤ) (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0<a) (hε : 0<ε) (hB : 0≤B) :
    ∃ n : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0<C ∧
      ∀ Z : ℝ, 1≤Z → ∀ χ : AngularCharacter, (Ideal.absNorm χ.modulus:ℝ)≤Z^B →
      ∀ t : ℝ, volumeControl k Q χ a b ha (normPowerProfile W a b ha hs hW t) ≤
        C*Z^ε*(1+‖t‖)^n := by
  obtain ⟨S,F,hF,hfourier⟩ := annular_fourier_control k a b ha
  obtain ⟨n,hn⟩ := normPowerProfile_uniform_degree a b ha S
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hprofile⟩ := hn W hs hW
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  have hm : 0≤mass := Nat.cast_nonneg _
  let A := D*mass*nonzeroLatticeEnvelopeConstant*F*C
  have he := nonzeroLatticeEnvelopeConstant_nonneg
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨1+A,by linarith,?_⟩
  intro Z hZ χ hnorm t
  have hheight : (1+‖t/(2*Real.pi)‖)^n ≤ (1+‖t‖)^n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have hf : fourierControl (annularCLM k a b ha (normPowerProfile W a b ha hs hW t)) ≤
      F*(C*(1+‖t‖)^n) :=
    (hfourier _).trans (mul_le_mul_of_nonneg_left hseminorm hF.le)
  have herr : volumeControl k Q χ a b ha (normPowerProfile W a b ha hs hW t) ≤
      (D*Z^ε)*(mass*(nonzeroLatticeEnvelopeConstant*(F*(C*(1+‖t‖)^n)))) := by
    unfold volumeControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf he) hm)
    · exact mul_nonneg hm (mul_nonneg he (fourierControl_nonneg _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D*Z^ε)*(mass*(nonzeroLatticeEnvelopeConstant*(F*(C*(1+‖t‖)^n)))) := herr
    _ = A*Z^ε*(1+‖t‖)^n := by dsimp [A];ring
    _ ≤ (1+A)*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

theorem normalized_actual_rectangle_estimate (k : ℤ)
    (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η χ ψ : AngularCharacter, ψ.k=k → (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      (Q ≤ ψ.modulus) → PrimaryVolume.InducedBy χ ψ →
      ∀ m A₀ z : O, (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, χ.elementCoeff n=CanonicalRowCompletion.rowTwist η.elementHom.toMonoidHom m 1 (A₀*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
          twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := volumeControl_polynomial_height k Q a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := volumeControl_polynomial_height k Q a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η χ ψ hk hnorm hQψ hind m A₀ z hmLam hm2 hrow t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl k Q χ a₁ b₁ ha₁ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl k Q χ a₂ b₂ ha₂ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  rw [hk] at hraw
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

end OAI.SevenEighths.Angular.TwistedVolume

#print axioms OAI.SevenEighths.Angular.TwistedVolume.normalized_actual_rectangle_estimate
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.TwistedVolume.normalized_actual_rectangle_estimate
