import AngularPhysicalFinite
import AngularPhysicalDetectorGammaCutoff
import OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic
import OAI.NumberTheory.DirichletL.Hecke.DetectorTail
import AngularPhysicalDetectorGammaUniform
import OAI.NumberTheory.DirichletL.GammaDetectorExpansion
import OAI.NumberTheory.DirichletL.Hecke.DetectorPartition
import OAI.NumberTheory.DirichletL.Hecke.DetectorFinite
import OAI.NumberTheory.DirichletL.Hecke.DetectorLower
import OAI.NumberTheory.DirichletL.Hecke.DetectorFourierActual
import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientBounds
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicSupport
import OAI.NumberTheory.DirichletL.Hecke.DetectorFrequency
import OAI.NumberTheory.DirichletL.Hecke.DetectorCommonFrequency
import OAI.NumberTheory.DirichletL.Hecke.DetectorNormalized


-- Proof bodies from AngularDetectorWitnessArithmeticRisk; initial SHA256 d2ecb45c053daa342f1f0a480e955b0100b11ef2c706e01ed15eb589f580d735

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation CompletedGauss
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open HeckeDetectorWitnessArithmetic (cutoffCoefficient cutoffCoefficient_tail)
theorem weighted_fiber (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (χ.idealHom) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (χ.idealHom) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (χ.idealHom) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, ite_eq_right hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

def exponentialTerm (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (χ.idealHom) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

theorem exponentialTerm_tail (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (χ.idealHom) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorTailRisk; initial SHA256 100763e16c072608b114b864ffa258cd5262fe2192f08e5ca0e2a0b0b9ac032f

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation CompletedGauss
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open HeckeDetectorWitnessArithmetic (cutoffCoefficient)
open HeckeDetectorTail (exponential_cubic_bound cutoffCoefficient_bound norm_weight_two)
lemma weighted_norm_le_one (χ : AngularCharacter) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (χ.idealHom) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖χ.idealHom I*CubicEisenstein.fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,CubicEisenstein.fullIdealWeight,ite_eq_right hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)<Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (χ.norm_idealHom_le_one I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

theorem exponentialTerm_bound (χ : AngularCharacter) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖exponentialTerm χ V D s Y I‖ ≤
      (768*B*Y^3)*‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : I = 0
  · simp [hI,exponentialTerm,cutoffCoefficient,CubicEisenstein.fullIdealWeight]
  have hN : (0 : ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(Y : ℂ))‖ =
      Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [exponentialTerm,norm_mul,norm_mul,he,norm_weight_two I hI]
  calc
    _ ≤ (128*B*(Ideal.absNorm I : ℝ))*Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul (cutoffCoefficient_bound V B hB hV D I)
        (weighted_norm_le_one χ s hs I) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ (128*B)*(6*Y^3/(Ideal.absNorm I : ℝ)^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exponential_cubic_bound _ Y hN hY) (by positivity)
    _ = _ := by ring

theorem exponentialTerm_summable (χ : AngularCharacter) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) : Summable (exponentialTerm χ V D s Y) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (768*B*Y^3)).of_norm_bounded (exponentialTerm_bound χ V B hB hV D Y hY s hs)

lemma cutoff_defect_bound (V : ℝ → ℂ) (B : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (x : ℝ) : ‖1-V x‖ ≤ 1+B :=
  (norm_sub_le _ _).trans (by simpa using add_le_add_left (hV x) 1)

def terminalRemainder (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    (1-T ((Ideal.absNorm I : ℝ)/U))

lemma exponentialTerm_half (χ : AngularCharacter) (V : ℝ → ℂ) (D Y : ℝ)
    (_hY : 0 < Y) (s : ℂ) (I : Ideal O) :
    exponentialTerm χ V D s Y I = exponentialTerm χ V D s (2*Y) I *
      Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))) := by
  unfold exponentialTerm
  rw [mul_assoc (cutoffCoefficient V D I * IdealEuler.weighted (χ.idealHom) s I),
    ←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem terminalRemainder_bound (χ : AngularCharacter) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re)
    (I : Ideal O) :
    ‖terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ U
  · rw [terminalRemainder,hTone _ (by positivity) ((div_le_one hU).mpr hI)]
    simp only [sub_self,mul_zero,norm_zero]
    positivity
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ)))‖ ≤
      Real.exp (-U/(2*Y)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc : (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))).re =
        -(Ideal.absNorm I : ℝ)/(2*Y) := by
      rw [show (2 : ℂ)*(Y : ℂ) = ((2*Y : ℝ) : ℂ) by push_cast; rfl,
        ←Complex.ofReal_neg,←Complex.ofReal_div,Complex.ofReal_re]
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith [lt_of_not_ge hI]) (by positivity)
  rw [terminalRemainder,exponentialTerm_half χ V D Y hY s I]
  simp only [norm_mul]
  have h1 := mul_le_mul
    (exponentialTerm_bound χ V B hB hV D (2*Y) (by positivity) s hs I) he
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul h1 (cutoff_defect_bound V B hV (2*(Ideal.absNorm I : ℝ)/D))
    (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 (cutoff_defect_bound T BT hT ((Ideal.absNorm I : ℝ)/U))
    (norm_nonneg _) (by positivity)
  apply h3.trans_eq
  ring

theorem terminalRemainder_summable (χ : AngularCharacter) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    Summable (terminalRemainder χ V T D Y U s) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))).of_norm_bounded
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)

theorem terminalRemainder_tsum_bound (χ : AngularCharacter) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∑' I, terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  have hsum := terminalRemainder_summable χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  rw [←tsum_mul_left]
  exact hsum.norm.tsum_le_tsum
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)
    ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left _)

theorem terminalRemainder_uniform_small (B BT ε : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : AngularCharacter) (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ B) → (∀ x : ℝ, ‖T x‖ ≤ BT) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ (D : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖∑' I, terminalRemainder χ V T D (U^20) (U^21) s I‖ < ε := by
  let C : ℝ := 6144*B*(1+B)*(1+BT)*(∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖)
  have ht : Tendsto (fun U : ℝ => C*(U^60*Real.exp (-U/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 60 (1/2) (by norm_num)).const_mul C
    convert h using 1
    · ext U
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      congr 2
      ring_nf
    · ring_nf
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ V T hV hT hTone D s hs
  have hUpos : 0 < U := by linarith
  have hb := terminalRemainder_tsum_bound χ V T B BT hB hBT hV hT hTone
    D (U^20) (U^21) (by positivity) (by positivity) s hs
  have he : -(U^21)/(2*U^20) = -U/2 := by
    rw [show U^21 = U^20*U by ring]
    field_simp
  have hp : (U^20)^3 = U^60 := by ring
  rw [he,hp] at hb
  have hC : (6144*B*U^60*(1+B)*(1+BT)*Real.exp (-U/2))*
      (∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖) = C*(U^60*Real.exp (-U/2)) := by
    dsimp [C]
    ring
  rw [hC] at hb
  exact hb.trans_lt (hU₀ U hU₀')

theorem exponential_sum_tail_unconditional (χ : AngularCharacter) (V : ℝ → ℂ)
    (B D Y : ℝ) (hB : 0 ≤ B) (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) :=
  exponential_sum_tail χ V D hD hV hVzero s Y
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs)

def terminalTerm (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    T ((Ideal.absNorm I : ℝ)/U)

private lemma summable_mul_bounded {A : Type*} (f g : A → ℂ)
    (hf : Summable f) (B : ℝ) (hg : ∀ a, ‖g a‖ ≤ B) :
    Summable (fun a => f a*g a) :=
  (hf.norm.mul_right B).of_norm_bounded (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg a) (norm_nonneg _))

theorem terminal_sum_identity (χ : AngularCharacter) (V T : ℝ → ℂ)
    (B BT D Y U : ℝ) (hB : 0 ≤ B)
    (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B) (hTbound : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) -
        ∑' I : Ideal O, terminalRemainder χ V T D Y U s I := by
  let f := fun I : Ideal O => exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))
  have hf : Summable f := summable_mul_bounded _ _
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs) (1+B)
    (fun I => cutoff_defect_bound V B hVbound _)
  have hr : Summable (terminalRemainder χ V T D Y U s) :=
    summable_mul_bounded f _ hf (1+BT) (fun I => cutoff_defect_bound T BT hTbound _)
  have hi : terminalTerm χ V T D Y U s = fun I => f I-terminalRemainder χ V T D Y U s I := by
    funext I
    dsimp [f,terminalTerm,terminalRemainder]
    ring
  rw [hi,hf.tsum_sub hr]
  rw [show (∑' I, f I) = (∑' I, exponentialTerm χ V D s Y I)-Complex.exp (-1/(Y : ℂ)) from
    exponential_sum_tail_unconditional χ V B D Y hB hVbound hD hY hV hVzero s hs]

theorem terminal_sum_finite (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ I ∈ ConcretePrimeRowBridge.idealsUpTo ⌈2*U⌉₊, terminalTerm χ V T D Y U s I := by
  apply tsum_eq_sum
  intro I hI
  by_cases hI0 : I = 0
  · simp [terminalTerm,exponentialTerm,cutoffCoefficient,hI0]
  have hN : (⌈2*U⌉₊ : ℝ) < Ideal.absNorm I := by
    have hn : ¬Ideal.absNorm I ≤ ⌈2*U⌉₊ := by
      intro hh
      apply hI
      exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0),hh⟩
    exact_mod_cast lt_of_not_ge hn
  have ht : T ((Ideal.absNorm I : ℝ)/U)=0 := by
    apply hTzero
    apply (le_div_iff₀ hU).mpr
    linarith [Nat.le_ceil (2*U)]
  simp only [terminalTerm,ht,mul_zero]

end OAI.SevenEighths.Angular.PhysicalDetectorWitness


end -- close the component noncomputable section

-- Proof bodies from AngularDetectorExpansionRisk; initial SHA256 e4d0cf247d7814cbfacc809c6573708131e18d8b2421e254c10a134edd2b09b8

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation CompletedGauss
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open PhysicalGammaDetector
open GammaZeroDetector (cutoffSet mem_cutoffSet)
open GammaDetectorExpansion (line line_re gammaTerm gamma_expansion)
theorem cutoffTerm_weighted (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      V ((J.absNorm : ℝ)/D) * IdealEuler.weighted (χ.idealHom) s J := by
  simp only [cutoffTerm, Dyadic.coefficient, ite_true,
    IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

theorem cutoffTerm_outside (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (J : Ideal O)
    (hJ : J ∉ cutoffSet D) : cutoffTerm χ V D J s = 0 := by
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_hasSum (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    HasSum (fun J : Ideal O => cutoffTerm χ V D J s) (cutoff χ V D s) :=
  hasSum_sum_of_ne_finset_zero (cutoffTerm_outside χ V hD hV s)

def expansionPairCoefficient (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (p : Ideal O × Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((p.1.absNorm : ℝ)/D) *
    χ.idealHom (p.1*p.2)

def pairNorm (p : Ideal O × Ideal O) : ℝ := (p.1*p.2).absNorm

theorem pairCoefficient_zero_norm (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ)
    (p : Ideal O × Ideal O) (hp : pairNorm p = 0) : expansionPairCoefficient χ V D p = 0 := by
  have hn : (p.1*p.2).absNorm = 0 := by unfold pairNorm at hp; exact_mod_cast hp
  have hzero := Ideal.absNorm_eq_zero_iff.mp hn
  rw [expansionPairCoefficient, hzero]
  rw [show (⊥ : Ideal O) = 0 from rfl, map_zero, mul_zero]

theorem pairTerm_eq (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (s : ℂ)
    (p : Ideal O × Ideal O) :
    expansionPairCoefficient χ V D p * (pairNorm p : ℂ)^(-s) =
      cutoffTerm χ V D p.1 s * IdealEuler.weighted (χ.idealHom) s p.2 := by
  rw [cutoffTerm_weighted]
  by_cases hp : p.1*p.2 = 0
  · have he : pairNorm p = 0 := by simp [pairNorm, hp]
    rw [pairCoefficient_zero_norm χ V D p he, zero_mul]
    rw [mul_assoc, ← map_mul, hp, map_zero, mul_zero]
  · rw [mul_assoc, ← map_mul]
    simp only [expansionPairCoefficient, pairNorm, Complex.ofReal_natCast,
      IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      CubicEisenstein.fullIdealWeight, ite_eq_right hp]
    ring

theorem pairTerm_summable_norm (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖expansionPairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)‖) := by
  simpa only [pairTerm_eq] using
    (cutoffTerm_hasSum χ V hD hV s).summable.norm.mul_norm
      (IdealEuler.weighted_summable_norm _ (χ.norm_idealHom_le_one) s hs)

theorem pairSeries_eq (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    (∑' p : Ideal O × Ideal O, expansionPairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)) =
      cutoff χ V D s * LFunction χ s := by
  simp_rw [pairTerm_eq]
  rw [← tsum_mul_tsum_of_summable_norm (cutoffTerm_hasSum χ V hD hV s).summable.norm
    (IdealEuler.weighted_summable_norm _ (χ.norm_idealHom_le_one) s hs)]
  rw [(cutoffTerm_hasSum χ V hD hV s).tsum_eq, LFunction_eq_series χ s hs]
  rfl

theorem pairMajorant_summable (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖expansionPairCoefficient χ V D p‖*(pairNorm p)^(-(ρ.re+2))) := by
  have h := pairTerm_summable_norm χ V hD hV (ρ+2) (by norm_num; linarith)
  apply h.congr
  intro p
  by_cases hp : pairNorm p = 0
  · simp [pairCoefficient_zero_norm χ V D p hp]
  · have hn : 0 < pairNorm p := lt_of_le_of_ne (by unfold pairNorm; positivity) (Ne.symm hp)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hn]
    simp only [neg_re, add_re]
    norm_num

theorem pairGamma_tsum (χ : AngularCharacter) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re)
    (Y t : ℝ) :
    (∑' p : Ideal O × Ideal O, gammaTerm (expansionPairCoefficient χ V D p) (pairNorm p) ρ Y t) =
      detectorIntegrand χ V D Y ρ (line t) := by
  have hs : 1 < (ρ+line t).re := by simp only [add_re, line_re]; linarith
  calc
    _ = (Y : ℂ)^(line t)*Gamma (line t)*
        (∑' p : Ideal O × Ideal O, expansionPairCoefficient χ V D p*(pairNorm p : ℂ)^(-(ρ+line t))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      unfold gammaTerm
      ring
    _ = _ := by rw [pairSeries_eq χ V hD hV _ hs]; unfold detectorIntegrand; ring

def pairExponential (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  expansionPairCoefficient χ V D p*(pairNorm p : ℂ)^(-ρ)*Complex.exp (-(pairNorm p : ℂ)/(Y : ℂ))

theorem detector_hasSum_pairs (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairExponential χ V D ρ Y) (detectorIntegral χ V D Y ρ) := by
  have h := gamma_expansion (expansionPairCoefficient χ V D) pairNorm
    (fun p => by unfold pairNorm; positivity) (pairCoefficient_zero_norm χ V D)
    ρ hY (pairMajorant_summable χ V hD hV hρ)
  unfold pairExponential detectorIntegral
  simpa only [pairGamma_tsum χ V hD hV hρ, line] using h

theorem detector_eq_double_sum (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    detectorIntegral χ V D Y ρ = ∑' J : Ideal O, ∑' K : Ideal O,
      (UniqueFactorizationMonoid.moebius J : ℂ) * V ((J.absNorm : ℝ)/D) *
      χ.idealHom (J*K) * (((J*K).absNorm : ℝ) : ℂ)^(-ρ) *
        Complex.exp (-(((J*K).absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
  have h := detector_hasSum_pairs χ V hD hY hV hρ
  rw [← h.tsum_eq, h.summable.tsum_prod]
  rfl

theorem pairExponential_zero_left (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (K : Ideal O) : pairExponential χ V D ρ Y (0,K) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_zero_right (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) : pairExponential χ V D ρ Y (J,0) = 0 := by
  unfold pairExponential
  rw [pairCoefficient_zero_norm χ V D _ (by simp [pairNorm]), zero_mul, zero_mul]

theorem pairExponential_fiber (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairExponential χ V D ρ Y p.val) =
      exponentialTerm χ V D ρ Y J := by
  have he (p : CompletedGauss.MulFiber J) :
      pairExponential χ V D ρ Y p.val =
        ((UniqueFactorizationMonoid.moebius p.val.1 : ℂ)*V ((p.val.1.absNorm : ℝ)/D)*
          IdealEuler.weighted (χ.idealHom) ρ (p.val.1*p.val.2))*
          Complex.exp (-((J.absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
    rw [pairExponential, pairTerm_eq, cutoffTerm_weighted, mul_assoc _ _
      (IdealEuler.weighted (χ.idealHom) ρ p.val.2), ← map_mul]
    congr 2
    rw [pairNorm, p.property]
  simp_rw [he]
  rw [tsum_mul_right, weighted_fiber]
  rfl

theorem detector_hasSum_convolution (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (exponentialTerm χ V D ρ Y)
      (detectorIntegral χ V D Y ρ) := by
  have h := (detector_hasSum_pairs χ V hD hY hV hρ).tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairExponential χ V D ρ Y p.val) _ at h
  simpa only [pairExponential_fiber] using h

theorem detector_large_product_tail (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    (∑' J : Ideal O, exponentialTerm χ V D ρ Y J *
      (1-V (2*(J.absNorm : ℝ)/D))) =
      detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ)) := by
  have h := detector_hasSum_convolution χ V (by linarith : 0 < D) hY hVzero hρ
  rw [exponential_sum_tail χ V D hD hV hVzero ρ Y h.summable,
    h.tsum_eq]

theorem pairExponential_summable_norm (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O => ‖pairExponential χ V D ρ Y p‖) :=
  (detector_hasSum_pairs χ V hD hY hV hρ).summable.norm

def pairTail (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairExponential χ V D ρ Y p * (1-V (2*pairNorm p/D))

theorem pairTail_summable (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (pairTail χ V D ρ Y) := by
  apply Summable.of_norm
  apply ((pairExponential_summable_norm χ V hD hY hVzero hρ).mul_right 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  rw [pairTail, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hn := norm_sub_le (1 : ℂ) (V (2*pairNorm p/D))
  rw [norm_one] at hn
  linarith [hV (2*pairNorm p/D)]

theorem pairTail_fiber (χ : AngularCharacter) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairTail χ V D ρ Y p.val) =
      exponentialTerm χ V D ρ Y J *
        (1-V (2*(J.absNorm : ℝ)/D)) := by
  have hn (p : CompletedGauss.MulFiber J) : pairNorm p.val = (J.absNorm : ℝ) := by
    rw [pairNorm, p.property]
  simp_rw [pairTail, hn]
  rw [tsum_mul_right, pairExponential_fiber]

theorem detector_eq_pair_tail (χ : AngularCharacter) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hVone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairTail χ V D ρ Y)
      (detectorIntegral χ V D Y ρ - Complex.exp (-1/(Y : ℂ))) := by
  have hs := pairTail_summable χ V (by linarith : 0 < D) hY hVzero hV hρ
  have hf := hs.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairTail χ V D ρ Y p.val) _ at hf
  simp_rw [pairTail_fiber] at hf
  have he := hf.tsum_eq
  rw [detector_large_product_tail χ V hD hY hVone hVzero hρ] at he
  exact he.symm ▸ hs.hasSum

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorPartitionRisk; initial SHA256 09861a95e115ab8a617ce7cdfbeb7958a3cbd3ea5c2a03839b3a0b8107a019a6

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation CompletedGauss
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open DyadicTransfer
open HeckeDetectorPartition (finite_pair_reassembly length norm_le_last_scale)
def pairCoefficient (χ : AngularCharacter) (V T : ℝ → ℂ)
    (D Y U : ℝ) (s : ℂ) (p : Ideal HeckeFamily.O × Ideal HeckeFamily.O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ)/D) *
    IdealEuler.weighted (χ.idealHom) s (p.1*p.2) *
    Complex.exp (-((Ideal.absNorm (p.1*p.2) : ℝ) : ℂ)/(Y : ℂ)) *
    (1-V (2*(Ideal.absNorm (p.1*p.2) : ℝ)/D)) * T ((Ideal.absNorm (p.1*p.2) : ℝ)/U)

theorem actual_pair_reassembly (χ : AngularCharacter) (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (D Y U X Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (s : ℂ)
    (S : Finset (Ideal HeckeFamily.O × Ideal HeckeFamily.O))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      (Ideal.absNorm p.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.2 : ℝ) ≤ Z) :
    (∑ p ∈ S, pairCoefficient χ V T D Y U s p) =
      ∑ j ∈ Finset.range (length X+1), ∑ k ∈ Finset.range (length Z+1), ∑ p ∈ S,
        pairCoefficient χ V T D Y U s p *
          annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k) := by
  apply finite_pair_reassembly S _ _ _ V hsmall hlarge
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).1),
      (hS p hp).2.2.1.trans (norm_le_last_scale X hX)⟩
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).2.1),
      (hS p hp).2.2.2.trans (norm_le_last_scale Z hZ)⟩

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorFiniteRisk; initial SHA256 256362175e1381fc3770626bee51d16fb6fdef480750c0447f2f7544ad63afa4

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation CompletedGauss
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open DyadicTransfer ConcretePrimeRowBridge
open HeckeDetectorWitnessArithmetic (cutoffCoefficient)
open HeckeDetectorPartition (length norm_le_last_scale exists_large_pair pair_scale_bounds)
open HeckeDetectorFinite (pairSet)
lemma pairCoefficient_zero_left (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (0,J) = 0 := by
  simp only [pairCoefficient,zero_mul,map_zero,mul_zero]

lemma pairCoefficient_zero_right (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (J,0) = 0 := by
  simp only [pairCoefficient,mul_zero,map_zero,zero_mul]

theorem pairCoefficient_support (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (p : Ideal O × Ideal O) (hp : p ∉ pairSet U) :
    pairCoefficient χ V T D Y U s p = 0 := by
  by_cases h1 : p.1 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h1]
    exact pairCoefficient_zero_left χ V T D Y U s p.2
  by_cases h2 : p.2 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h2]
    exact pairCoefficient_zero_right χ V T D Y U s p.1
  have hprod : p.1*p.2 ≠ 0 := mul_ne_zero h1 h2
  have hnpos : 0 < Ideal.absNorm (p.1*p.2) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hprod)
  have hnorm : 2*U ≤ (Ideal.absNorm (p.1*p.2) : ℝ) := by
    by_contra h
    have hb : Ideal.absNorm (p.1*p.2) ≤ ⌈2*U⌉₊ := by
      exact_mod_cast (le_trans (lt_of_not_ge h).le (Nat.le_ceil (2*U)))
    have hh1 : Ideal.absNorm p.1 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_right p.1 p.2))
    have hh2 : Ideal.absNorm p.2 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_left p.2 p.1))
    apply hp
    exact Finset.mem_product.mpr
      ⟨mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h1),hh1.trans hb⟩,
       mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h2),hh2.trans hb⟩⟩
  have hz := hT ((Ideal.absNorm (p.1*p.2) : ℝ)/U) ((le_div_iff₀ hU).mpr hnorm)
  simp only [pairCoefficient,hz,mul_zero]

theorem pair_fiber (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val) =
      terminalTerm χ V T D Y U s I := by
  have h := weighted_fiber χ V D s I
  unfold terminalTerm exponentialTerm
  rw [←h,←tsum_mul_right,←tsum_mul_right,←tsum_mul_right]
  apply tsum_congr
  intro p
  simp only [pairCoefficient,p.property]

theorem terminal_sum_eq_pair_sum (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p := by
  have hfinite : Function.HasFiniteSupport (pairCoefficient χ V T D Y U s) := by
    apply (pairSet U).finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (pairCoefficient_support χ V T D Y U hU hT s p hn)
  have hsum := (summable_of_hasFiniteSupport hfinite).hasSum.tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun I : Ideal O => ∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val)
    (∑' p, pairCoefficient χ V T D Y U s p) at hsum
  simp_rw [pair_fiber] at hsum
  rw [hsum.tsum_eq]
  exact tsum_eq_sum (pairCoefficient_support χ V T D Y U hU hT s)

def dyadicBlock (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (j k : ℕ) : ℂ :=
  ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k)

theorem terminal_sum_eq_dyadic (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        ∑ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1), dyadicBlock χ V T D Y U s j k := by
  have hX : (0 : ℝ) < ⌈2*U⌉₊ := lt_of_lt_of_le (by positivity) (Nat.le_ceil (2*U))
  rw [terminal_sum_eq_pair_sum χ V T D Y U hU hT s]
  apply actual_pair_reassembly χ V T hV hVzero D Y U _ _ hX hX s
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1,hp1b⟩ := mem_idealsUpTo.mp h1
  obtain ⟨hp2,hp2b⟩ := mem_idealsUpTo.mp h2
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega),
    Ideal.absNorm_eq_zero_iff.not.mp (by omega),by exact_mod_cast hp1b,by exact_mod_cast hp2b⟩

theorem exists_dyadic_block (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (c : ℝ)
    (hc : c ≤ ‖∑' I : Ideal O, terminalTerm χ V T D Y U s I‖) :
    ∃ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
      ∃ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        c ≤ (((length (⌈2*U⌉₊ : ℝ)+1 : ℕ) : ℝ)^2)*‖dyadicBlock χ V T D Y U s j k‖ := by
  rw [terminal_sum_eq_dyadic χ V T D Y U hU hT hV hVzero s] at hc
  obtain ⟨j,hj,k,hk,hb⟩ := exists_large_pair (length (⌈2*U⌉₊ : ℝ))
    (length (⌈2*U⌉₊ : ℝ)) (dyadicBlock χ V T D Y U s)
  exact ⟨j,hj,k,hk,by simpa only [pow_two] using hc.trans hb⟩

theorem nonzero_block_scale_bounds (χ : AngularCharacter) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hD : 0 < D) (hU : 0 < U)
    (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (j k : ℕ)
    (hb : dyadicBlock χ V T D Y U s j k ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨p,hp,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hk := (mul_ne_zero_iff.mp hne).2
  have hj := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  simp only [pairCoefficient,ne_eq,mul_eq_zero,not_or] at hc
  obtain ⟨⟨⟨⟨⟨hmu,hfirst⟩,hweight⟩,hexp⟩,hproduct⟩,hterminal⟩ := hc
  apply pair_scale_bounds V T hV hVzero hT
    (Ideal.absNorm p.1) (Ideal.absNorm p.2) D U (by positivity) (by positivity)
    hD hU j k hj hk hfirst
  · simpa only [map_mul,Nat.cast_mul] using hproduct
  · simpa only [map_mul,Nat.cast_mul] using hterminal

end OAI.SevenEighths.Angular.PhysicalDetectorWitness


end -- close the component noncomputable section

-- Proof bodies from AngularDetectorLowerRisk; initial SHA256 0697814c0c3a15e600fc57938eb3cb1a0b7397101cdf003f3a9c9054372d798b

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation CompletedGauss
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open PhysicalGammaDetector
open HeckeDetectorLower (unit_term_lower)
open HeckeDetectorPartition (length)
theorem terminal_uniform_lower (angularOrder : ℕ) (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : AngularCharacter), χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      (1/2 : ℝ) ≤ ‖∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I‖ := by
  obtain ⟨UG,hUG⟩ := PhysicalGammaDetector.detector_uniform_small angularOrder R θ (1/8) hR hθ hθ' (by norm_num)
  obtain ⟨UT,hUT⟩ := terminalRemainder_uniform_small 1 1 (1/8) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max 2 (max UG UT),?_⟩
  intro U hU χ horder hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hg := hUG U ((le_max_left UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ horder hχ V hVb D (by linarith) hDU hQ ρ hρ hzero hheight
  have ht := hUT U ((le_max_right UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ V T hVb hTb hTone D ρ (by linarith)
  have hi := terminal_sum_identity χ V T 1 1 D (U^20) (U^21) (by norm_num)
    hVb hTb hD (by positivity) hVone hVzero ρ (by linarith)
  rw [(detector_hasSum_convolution χ V
    (by linarith : 0 < D) (by positivity : 0 < U^20) hVzero (by linarith : -1 < ρ.re)).tsum_eq] at hi
  have he : Complex.exp (-1/((U^20 : ℝ) : ℂ)) =
      detectorIntegral χ V D (U^20) ρ -
        (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I) -
        (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I) := by
    rw [hi]
    ring
  have hn := norm_sub_le
    (detectorIntegral χ V D (U^20) ρ - ∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
    (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I)
  rw [←he] at hn
  have hn' := norm_sub_le (detectorIntegral χ V D (U^20) ρ)
    (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
  have hu := unit_term_lower U hU2
  linarith

theorem exists_dyadic_zero_witness (angularOrder : ℕ) (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : AngularCharacter), χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          (1/2 : ℝ) ≤ 625*(Real.logb 2 U)^2*‖dyadicBlock χ V T D (U^20) (U^21) ρ j k‖ ∧
          (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
          (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨U₁,hU₁⟩ := terminal_uniform_lower angularOrder R θ hR hθ hθ'
  refine ⟨max 2 U₁,?_⟩
  intro U hU χ horder hχ V T hVb hTb hVone hVzero hTone hTzero D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hUpos : 0 < U := by linarith
  have ht := hU₁ U ((le_max_right _ _).trans hU) χ horder hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,hb⟩ := exists_dyadic_block χ V T D (U^20) (U^21)
    (by positivity) hTzero hVone hVzero ρ (1/2) ht
  have hbn : dyadicBlock χ V T D (U^20) (U^21) ρ j k ≠ 0 := by
    intro hz
    rw [hz,norm_zero,mul_zero] at hb
    norm_num at hb
  refine ⟨j,hj,k,hk,?_,nonzero_block_scale_bounds χ V T D (U^20) (U^21)
    (by linarith) (by positivity) hTzero hVone hVzero ρ j k hbn⟩
  exact hb.trans (mul_le_mul_of_nonneg_right
    (HeckeDetectorBudget.source_pair_count_bound U hU2) (norm_nonneg _))

end OAI.SevenEighths.Angular.PhysicalDetectorWitness


end -- close the component noncomputable section

-- Proof bodies from AngularDetectorFourierRisk; initial SHA256 04fb413fdcf5ff2e8022886d5a03c853134bbfb0d5b98cdfeabc83d03de932f6

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorProfiles HeckeDetectorFourier
def inverseCoefficient (χ : AngularCharacter) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (χ.idealHom) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : AngularCharacter) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (χ.idealHom) s I*W ((Ideal.absNorm I : ℝ)/N)

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : AngularCharacter) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

theorem actual_finite_pair_separation (χ : AngularCharacter) (Ω V T W₁ W₂ : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩs : ContDiff ℝ ∞ Ω)
    (hVs : ContDiff ℝ ∞ V) (hTs : ContDiff ℝ ∞ T)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (S R : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ J ∈ R, J ≠ 0)
    (hΩ : ∀ I ∈ S, ∀ J ∈ R,
      W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    (∑ I ∈ S, ∑ J ∈ R, pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N)) =
      ∫ t : ℝ,
        (𝓕 (logSource Ω V T hΩc hΩs hVs hTs (2*D*N/Dstar) (D*N/Y) (D*N/U))) t*
        phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
          (fun I => Real.log ((Ideal.absNorm I : ℝ)/D)) t*
        phasePolynomial R (plainCoefficient χ W₂ N s)
          (fun J => Real.log ((Ideal.absNorm J : ℝ)/N)) t := by
  rw [← finite_pair_separation]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  exact actual_pair_profile χ Ω V T W₁ W₂ Dstar D N Y U hD hN s I J
    (hS I hI) (hR J hJ) (hΩ I hI J hJ)

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorCoefficientRisk; initial SHA256 fcf5547420164a348fc4640f57465b8fedb40e6e2f3548642e449743bff327ee

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorCoefficientBounds (annular_norm_le_two expandedSet expandedSet_count)
lemma inverseCoefficient_norm_le_two (χ : AngularCharacter) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (Dstar D : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖ ≤ 2 := by
  simp only [inverseCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*1*1*2 := by
      gcongr
      · exact CubicEisenstein.norm_ideal_moebius_le_one I
      · exact weighted_norm_le_one χ s hs I
      · exact hV _
      · exact annular_norm_le_two V hV _
    _ = _ := by norm_num

lemma plainCoefficient_norm_le_two (χ : AngularCharacter) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (N : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖ ≤ 2 := by
  simp only [plainCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*2 := mul_le_mul (weighted_norm_le_one χ s hs I)
      (annular_norm_le_two V hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num
theorem coefficient_mass (χ : AngularCharacter) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (U Dstar D N : ℝ) (hU : 1 ≤ U) (s : ℂ) (hs : 0 ≤ s.re) :
    ((∑ I ∈ expandedSet U, ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖)*
      (∑ I ∈ expandedSet U, ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖)) ≤
      67108864*U^42 := by
  have hi : (∑ I ∈ expandedSet U,
      ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => inverseCoefficient_norm_le_two χ V hV Dstar D s hs I)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hp : (∑ I ∈ expandedSet U,
      ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => plainCoefficient_norm_le_two χ V hV N s hs I)
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hh := mul_le_mul hi hp
    (Finset.sum_nonneg (fun I hI => norm_nonneg _)) (by positivity)
  apply hh.trans_eq
  ring

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorBridgeRisk; initial SHA256 4beeff1537a03a97f836a9556f32788246bbe02354042081295ae6cd0a85e06e

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorFourier (phasePolynomial)
open HeckeDetectorDyadicBridge (norm_phase normalization inverseProfile inverseProfile_at_norm normalization_norm)
lemma weighted_eq (χ : AngularCharacter) (s : ℂ) (J : Ideal O) (hJ : J≠0) :
    IdealEuler.weighted (χ.idealHom) s J=χ.idealHom J*(J.absNorm : ℂ)^(-s) := by
  simp only [IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]

theorem plain_phase_eq (χ : AngularCharacter) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (plainCoefficient χ W D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*polynomial χ false W D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ false W D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [plainCoefficient, weighted_eq χ s J (hS J hJ)]
  rfl

theorem inverse_phase_eq (χ : AngularCharacter) (V W : ℝ→ℂ) (Dstar D : ℝ) (hD : 0<D)
    (s : ℂ) (t : ℝ) (S : Finset (Ideal O)) (hS : ∀ J∈S, J≠0)
    (hcover : ∀ J : Ideal O, J≠0 → inverseProfile V W Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    phasePolynomial S (inverseCoefficient χ V W Dstar D s)
      (fun J => Real.log ((J.absNorm : ℝ)/D)) t =
      (D : ℂ)^((1/2 : ℂ)-s)*
        polynomial χ true (inverseProfile V W Dstar D) D s.re (2*Real.pi*t-s.im) := by
  rw [← phase_sum_eq_polynomial χ true (inverseProfile V W Dstar D) D hD s t S hS hcover]
  unfold phasePolynomial
  apply Finset.sum_congr rfl
  intro J hJ
  rw [inverseCoefficient, weighted_eq χ s J (hS J hJ), inverseProfile_at_norm V W Dstar D _ hD]
  simp only [coefficient, ite_true]
  ring

theorem pair_phase_norm (χ : AngularCharacter) (V W₁ W₂ : ℝ→ℂ) (Dstar D N : ℝ)
    (hD : 0<D) (hN : 0<N) (s : ℂ) (t : ℝ) (S R : Finset (Ideal O))
    (hS : ∀ J∈S, J≠0) (hR : ∀ J∈R, J≠0)
    (hcoverS : ∀ J : Ideal O, J≠0 → inverseProfile V W₁ Dstar D ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (hcoverR : ∀ J : Ideal O, J≠0 → W₂ ((J.absNorm : ℝ)/N)≠0 → J∈R) :
    ‖phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
        (fun J => Real.log ((J.absNorm : ℝ)/D)) t‖ *
      ‖phasePolynomial R (plainCoefficient χ W₂ N s)
        (fun J => Real.log ((J.absNorm : ℝ)/N)) t‖ =
      D^(1/2-s.re)*N^(1/2-s.re)*
        (‖polynomial χ true (inverseProfile V W₁ Dstar D) D s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false W₂ N s.re (2*Real.pi*t-s.im)‖) := by
  rw [inverse_phase_eq χ V W₁ Dstar D hD s t S hS hcoverS,
    plain_phase_eq χ W₂ N hN s t R hR hcoverR,
    norm_mul, norm_mul, normalization_norm D hD s, normalization_norm N hN s]
  ring

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorFourierSupportRisk; initial SHA256 fbc6b09d2afe9b871693951b599020c23bbfa878cb5d2dd01a88ba65aecc52e2

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorDyadicBridge (fourierSet pairSet_subset_fourier)
theorem dyadicBlock_eq_fourier_rectangle (χ : AngularCharacter) (V T : ℝ→ℂ)
    (D Y U : ℝ) (hU : 0<U) (hT : ∀ x : ℝ, 2≤x → T x=0)
    (s : ℂ) (j k : ℕ) :
    dyadicBlock χ V T D Y U s j k =
      ∑ J∈fourierSet U, ∑ K∈fourierSet U,
        pairCoefficient χ V T D Y U s (J,K)*
          DyadicTransfer.annularCutoff V ((J.absNorm : ℝ)/(2 : ℝ)^j)*
          DyadicTransfer.annularCutoff V ((K.absNorm : ℝ)/(2 : ℝ)^k) := by
  unfold dyadicBlock
  calc
    _ = ∑ p∈fourierSet U ×ˢ fourierSet U,
        pairCoefficient χ V T D Y U s p *
          DyadicTransfer.annularCutoff V ((p.1.absNorm : ℝ)/(2 : ℝ)^j) *
          DyadicTransfer.annularCutoff V ((p.2.absNorm : ℝ)/(2 : ℝ)^k) := by
      apply Finset.sum_subset (pairSet_subset_fourier U hU.le)
      intro p hp hn
      rw [pairCoefficient_support χ V T D Y U hU hT s p hn, zero_mul, zero_mul]
    _ = _ := Finset.sum_product _ _ _

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorFrequencyRisk; initial SHA256 65a21c9c504e8ebbeb9ac0a7aa54f715bde0c9fe6f03fe1606f2178e4c115d8f

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds (expandedSet)
open HeckeDetectorDyadicBridge (fourierSet_nonzero)
theorem dyadic_frequency_bound (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L)
    (hΩone : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      DyadicTransfer.annularCutoff cutoff x ≠ 0 →
      DyadicTransfer.annularCutoff cutoff y ≠ 0 → Ω (Real.log x+Real.log y)=1)
    (n : ℕ) :
    ∃ C₀ Cn : ℝ, 1 ≤ C₀ ∧ 0 ≤ Cn ∧ ∀ (U Dstar F : ℝ),
      1 ≤ U → 0 < Dstar → 0 < F → ∀ (χ : AngularCharacter) (s : ℂ), 0 ≤ s.re →
      ∀ j k : ℕ, ∃ t : ℝ, ‖t‖ ≤ F ∧
        ‖dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k‖ ≤
          (67108864*U^42)*Cn/F^n + C₀*
            ‖phasePolynomial (expandedSet U)
                (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar ((2 : ℝ)^j) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
              phasePolynomial (expandedSet U)
                (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t‖ := by
  obtain ⟨C₀,hC₀,hb₀⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow 0
  obtain ⟨Cn,hCn,hbn⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow n
  refine ⟨1+C₀,Cn,by linarith,hCn,?_⟩
  intro U Dstar F hU hDstar hF χ s hs j k
  let D : ℝ := (2 : ℝ)^j
  let N : ℝ := (2 : ℝ)^k
  let a := inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s
  let b := plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) N s
  let x := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/D)
  let y := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/N)
  let g := logSource Ω cutoff cutoff hΩc hΩ (cutoff.smooth ⊤) (cutoff.smooth ⊤)
    (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
  have hUpos : 0 < U := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have heq : dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k =
      ∑ I ∈ expandedSet U, ∑ J ∈ expandedSet U, a I*b J*g (x I+y J) := by
    rw [dyadicBlock_eq_fourier_rectangle χ cutoff cutoff Dstar (U^20) (U^21)
      (by positivity) cutoff_zero s j k]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact actual_pair_profile χ Ω cutoff cutoff (DyadicTransfer.annularCutoff cutoff)
      (DyadicTransfer.annularCutoff cutoff) Dstar D N (U^20) (U^21) hD hN s I J
      (fourierSet_nonzero _ I hI) (fourierSet_nonzero _ J hJ)
      (hΩone _ _ (by positivity) (by positivity))
  obtain ⟨t,ht,hb⟩ := exists_bounded_frequency (expandedSet U) (expandedSet U) a b x y g F hF n
  refine ⟨t,ht,?_⟩
  rw [heq]
  have hg₀ : (∫ t : ℝ, ‖(𝓕 g) t‖) ≤ C₀ := by
    simpa only [pow_zero,one_mul] using hb₀ (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
      (by positivity) (by positivity) (by positivity)
  have hgn : (∫ t : ℝ, (1+‖t‖)^n*‖(𝓕 g) t‖) ≤ Cn :=
    hbn (2*D*N/Dstar) (D*N/U^20) (D*N/U^21) (by positivity) (by positivity) (by positivity)
  have hmass := coefficient_mass χ cutoff cutoff_norm_le U Dstar D N hU s hs
  apply hb.trans
  apply add_le_add
  · calc
      _ ≤ ((67108864*U^42)/F^n)*Cn := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmass (by positivity)
        · exact hgn
        · exact integral_nonneg (fun t => by positivity)
        · positivity
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (hg₀.trans (by linarith)) (norm_nonneg _)

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorCommonFrequencyRisk; initial SHA256 2b69cc4495b3edb775af27f39127dc353b2fb1d420f5d9fdd3b356964dccab53

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds (expandedSet)
open HeckeDetectorPartition (length)
open HeckeDetectorFrequency (exists_frequency_tail_order)
def phaseProduct (χ : AngularCharacter) (D U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ) : ℂ :=
  phasePolynomial (expandedSet U)
    (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) D ((2 : ℝ)^j) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
  phasePolynomial (expandedSet U)
    (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t

theorem exists_common_frequency_witness (angularOrder : ℕ) (R θ τ : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hτ : 0 < τ) :
    ∃ C U₀ : ℝ, 0 < C ∧ ∀ U : ℝ, U₀ ≤ U →
      ∀ χ : AngularCharacter, χ.k.natAbs≤angularOrder → (χ.k ≠ 0 ∨ χ.residue ≠ 1) → ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖ ≤ U^τ ∧
            1 ≤ C*(Real.logb 2 U)^2*‖phaseProduct χ D U ρ j k t‖ ∧
            (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨Ω,hΩc,hΩ,hwindow,hΩone⟩ := exists_product_log_cutoff
  obtain ⟨n,hn⟩ := exists_frequency_tail_order τ hτ
  have hL : 0 ≤ 2*Real.log 2+1 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  obtain ⟨C₀,Cn,hC₀,hCn,hfreq⟩ := dyadic_frequency_bound Ω hΩc hΩ
    (2*Real.log 2+1) hL hwindow hΩone n
  obtain ⟨UF,hUF⟩ := hn Cn
  obtain ⟨UL,hUL⟩ := exists_dyadic_zero_witness angularOrder R θ hR hθ hθ'
  refine ⟨2500*C₀,max 2 (max UF UL),by positivity,?_⟩
  intro U hU χ horder hχ D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  obtain ⟨j,hj,k,hk,hblock,hsupport⟩ :=
    hUL U ((le_max_right UF UL).trans ((le_max_right 2 _).trans hU))
      χ horder hχ cutoff cutoff cutoff_norm_le cutoff_norm_le cutoff_one cutoff_zero cutoff_one cutoff_zero
      D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨t,ht,hb⟩ := hfreq U D (U^τ) hU1 (by linarith) (by positivity) χ ρ (by linarith) j k
  have htail := hUF U ((le_max_left UF UL).trans ((le_max_right 2 _).trans hU)) hU1
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 625*(Real.logb 2 U)^2 by positivity)
  refine ⟨j,hj,k,hk,t,ht,?_,hsupport⟩
  change ‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖ at hb
  change (625*(Real.logb 2 U)^2)*‖dyadicBlock χ cutoff cutoff D (U^20) (U^21) ρ j k‖ ≤
    (625*(Real.logb 2 U)^2)*((67108864*U^42)*Cn/(U^τ)^n+C₀*‖phaseProduct χ D U ρ j k t‖) at hb'
  nlinarith

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section

-- Proof bodies from AngularDetectorNormalizedRisk; initial SHA256 e9ea5ac3f4d21311428b303390851e8441bddbcb8bc3b8cc82cd2f7e09186464

noncomputable section
open scoped Classical BigOperators Topology ContDiff FourierTransform SchwartzMap
open Set Filter Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorWitness
open FamilyContinuation OAI.SevenEighths.Angular.Dyadic
open HeckeDetectorProfiles HeckeDetectorFourier HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicBridge (fourierSet fourierSet_nonzero scales_le_eight_terminal inverse_annular_covered annular_covered)
lemma plainCoefficient_positive (χ : AngularCharacter) (D : ℝ) (hD : 0<D) (s : ℂ) :
    plainCoefficient χ positiveAnnular D s=
      plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) D s := by
  funext J
  unfold plainCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

lemma inverseCoefficient_positive (χ : AngularCharacter) (Dstar D : ℝ) (hD : 0<D) (s : ℂ) :
    inverseCoefficient χ cutoff positiveAnnular Dstar D s=
      inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s := by
  funext J
  unfold inverseCoefficient
  rw [positiveAnnular_eq _ (div_nonneg (Nat.cast_nonneg _) hD.le)]

theorem phaseProduct_norm (χ : AngularCharacter) (Dstar U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    ‖phaseProduct χ Dstar U s j k t‖ =
      ((2 : ℝ)^j)^(1/2-s.re)*((2 : ℝ)^k)^(1/2-s.re)*
        (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
            ((2 : ℝ)^j) s.re (2*Real.pi*t-s.im)‖ *
         ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) s.re (2*Real.pi*t-s.im)‖) := by
  obtain ⟨hj,hk⟩ := scales_le_eight_terminal (U^21) j k hprod
  have hDj : 0<(2 : ℝ)^j := by positivity
  have hNk : 0<(2 : ℝ)^k := by positivity
  unfold phaseProduct
  rw [norm_mul, ← inverseCoefficient_positive χ Dstar ((2 : ℝ)^j) hDj s,
    ← plainCoefficient_positive χ ((2 : ℝ)^k) hNk s]
  exact pair_phase_norm χ cutoff positiveAnnular positiveAnnular Dstar ((2 : ℝ)^j) ((2 : ℝ)^k)
    hDj hNk s t (fourierSet (U^21)) (fourierSet (U^21))
    (fourierSet_nonzero (U^21)) (fourierSet_nonzero (U^21))
    (inverse_annular_covered (U^21) ((2 : ℝ)^j) Dstar hDj hj cutoff positiveAnnular positiveAnnular_zero)
    (annular_covered (U^21) ((2 : ℝ)^k) hNk hk positiveAnnular positiveAnnular_zero)

theorem exists_normalized_product (angularOrder : ℕ) (R θ τ : ℝ) (hR : 0≤R)
    (hθ : 0≤θ) (hθ' : θ<3/4) (hτ : 0<τ) :
    ∃ C U₀ : ℝ, 0<C ∧ ∀ U : ℝ, U₀≤U →
      ∀ χ : AngularCharacter, χ.k.natAbs≤angularOrder → (χ.k≠0 ∨ χ.residue≠1) → ∀ Dstar : ℝ, 2≤Dstar → Dstar≤U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ)≤R*U → ∀ ρ : ℂ,
      (51/100 : ℝ)≤ρ.re → LFunction χ ρ=0 → |ρ.im|≤U^θ →
      ∃ j∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k∈Finset.range (HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1),
          ∃ t : ℝ, ‖t‖≤U^τ ∧
            1≤C*(Real.logb 2 U)^2*((2 : ℝ)^j)^(1/2-ρ.re)*((2 : ℝ)^k)^(1/2-ρ.re)*
              (‖polynomial χ true (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((2 : ℝ)^j))
                  ((2 : ℝ)^j) ρ.re (2*Real.pi*t-ρ.im)‖ *
               ‖polynomial χ false positiveAnnular ((2 : ℝ)^k) ρ.re (2*Real.pi*t-ρ.im)‖) ∧
            (2 : ℝ)^j<4*Dstar ∧ Dstar/8<(2 : ℝ)^j*(2 : ℝ)^k ∧
            (2 : ℝ)^j*(2 : ℝ)^k<8*U^21 := by
  obtain ⟨C,U₀,hC,hbound⟩ := exists_common_frequency_witness angularOrder R θ τ hR hθ hθ' hτ
  refine ⟨C,U₀,hC,?_⟩
  intro U hU χ horder hχ Dstar hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,t,ht,hb,hd,hn,hprod⟩ := hbound U hU χ horder hχ Dstar hD hDU hQ ρ hρ hzero hheight
  refine ⟨j,hj,k,hk,t,ht,?_,hd,hn,hprod⟩
  rw [phaseProduct_norm χ Dstar U ρ j k t hprod] at hb
  convert hb using 1; ring

end OAI.SevenEighths.Angular.PhysicalDetectorWitness

end -- close the component noncomputable section


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.weighted_fiber
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.weighted_fiber

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_tail
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_tail

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponential_sum_tail
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponential_sum_tail

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.weighted_norm_le_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.weighted_norm_le_one

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_summable

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoff_defect_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoff_defect_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_half
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponentialTerm_half

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_summable

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_tsum_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_tsum_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_uniform_small
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminalRemainder_uniform_small

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponential_sum_tail_unconditional
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exponential_sum_tail_unconditional

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_identity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_identity

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_finite
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_finite

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoffTerm_weighted
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoffTerm_weighted

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoffTerm_outside
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoffTerm_outside

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoffTerm_hasSum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.cutoffTerm_hasSum

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_zero_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_zero_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTerm_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTerm_eq

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTerm_summable_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTerm_summable_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairSeries_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairSeries_eq

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairMajorant_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairMajorant_summable

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairGamma_tsum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairGamma_tsum

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_hasSum_pairs
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_hasSum_pairs

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_eq_double_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_eq_double_sum

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_zero_left
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_zero_left

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_zero_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_zero_right

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_fiber
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_fiber

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_hasSum_convolution
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_hasSum_convolution

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_large_product_tail
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_large_product_tail

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_summable_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairExponential_summable_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTail_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTail_summable

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTail_fiber
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairTail_fiber

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_eq_pair_tail
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.detector_eq_pair_tail

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.actual_pair_reassembly
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.actual_pair_reassembly

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_zero_left
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_zero_left

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_zero_right
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_zero_right

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pairCoefficient_support

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pair_fiber
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pair_fiber

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_eq_pair_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_eq_pair_sum

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_eq_dyadic
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_sum_eq_dyadic

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_dyadic_block
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_dyadic_block

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.nonzero_block_scale_bounds
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.nonzero_block_scale_bounds

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_uniform_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.terminal_uniform_lower

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_dyadic_zero_witness
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_dyadic_zero_witness

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.scaled_exp_log_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.scaled_exp_log_product

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.actual_pair_profile
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.actual_pair_profile

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.actual_finite_pair_separation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.actual_finite_pair_separation

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.inverseCoefficient_norm_le_two
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.inverseCoefficient_norm_le_two

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.plainCoefficient_norm_le_two
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.plainCoefficient_norm_le_two

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.coefficient_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.coefficient_mass

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.weighted_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.weighted_eq

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.plain_phase_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.plain_phase_eq

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.inverse_phase_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.inverse_phase_eq

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.pair_phase_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.pair_phase_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.dyadicBlock_eq_fourier_rectangle
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.dyadicBlock_eq_fourier_rectangle

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.dyadic_frequency_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.dyadic_frequency_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_common_frequency_witness
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_common_frequency_witness

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.plainCoefficient_positive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.plainCoefficient_positive

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.inverseCoefficient_positive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.inverseCoefficient_positive

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.phaseProduct_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.phaseProduct_norm

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_normalized_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorWitness.exists_normalized_product
