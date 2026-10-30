import AngularPhysicalVolumeHeight
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.FiniteProfileExceptional
open TwistedVolume PrimaryVolume PlainRows AnnularSchwartz PlaneVolume
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight
open EisensteinSchwartzPoisson IdealMobiusDivisorSum
open CenteredMomentFiniteProfileExceptional
open CenteredMomentHeckeVolume (fixedPeriod fixedPeriod_ne_zero)
local notation "O" => ActualEisensteinCubic.O

theorem volumeControl_source_control (angularType : ℤ) (a b ε B : ℝ)
    (ha : 0<a) (hε : 0<ε) (hB : 0≤B) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, ∃ C : ℝ, 0<C ∧
      ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀ Z : ℝ, 1≤Z → ∀ χ : AngularCharacter,
      (χ.modulus.absNorm:ℝ)≤Z^B → ∀ t : ℝ,
      volumeControl angularType Q χ a b ha (normPowerProfile W a b ha hs (W.smooth ⊤) t)≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
  obtain ⟨S₀,F,hF,hfourier⟩ := annular_fourier_control angularType a b ha
  obtain ⟨n,T,C,hC,hprofile⟩ := normPowerProfile_source_control a b ha S₀
  obtain ⟨D,hD,hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  let S := insert (0,0) T
  refine ⟨n,S,by simp [S],?_⟩
  intro Q
  let mass : ℝ := Nat.card (O⧸Ideal.span {fixedPeriod Q})
  let A : ℝ := D*mass*nonzeroLatticeEnvelopeConstant*F*C
  have hmass : 0≤mass := Nat.cast_nonneg _
  have he := nonzeroLatticeEnvelopeConstant_nonneg
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨1+A,by linarith,?_⟩
  intro W hs Z hZ χ hχ t
  have hTS : T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro z hz
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hz)
  have hp := (hprofile W hs t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS hC.le) (by positivity))
  have hf : fourierControl (annularCLM angularType a b ha
      (normPowerProfile W a b ha hs (W.smooth ⊤) t))≤
      F*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n) :=
    (hfourier _).trans (mul_le_mul_of_nonneg_left hp hF.le)
  have herr : volumeControl angularType Q χ a b ha
      (normPowerProfile W a b ha hs (W.smooth ⊤) t)≤
      (D*Z^ε)*(mass*(nonzeroLatticeEnvelopeConstant*
        (F*(C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(1+‖t‖)^n)))) := by
    unfold volumeControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hχ)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf he) hmass)
    · exact mul_nonneg hmass (mul_nonneg he (fourierControl_nonneg _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  calc
    _≤_ := herr
    _=A*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by dsimp [A];ring
    _≤(1+A)*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
      gcongr
      linarith

end OAI.SevenEighths.Angular.FiniteProfileExceptional

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptional.volumeControl_source_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptional.volumeControl_source_control
