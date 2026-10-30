import AngularCanonicalCoefficient

/-! The finite projector for a canonical multiplicative coefficient.
Adapted from the fully inspected, pinned S3 AngularFiniteProjector proof.
Only the finite factor Phi is periodic. Its angular twist is not declared periodic.
These are physical Fourier identities, not moment estimates or L-function theorems. -/

noncomputable section
open scoped Classical BigOperators
namespace OAI.CubicEisenstein.AngularCanonicalProjector
open CompletedGauss ConcreteTraceCRT EisensteinEmbedding CubicJacobiGlobal
open SevenEighths.Angular AngularCompletedCoefficient AngularProfileDirichlet
open AngularBesselClosure AngularBesselDerivatives AngularHigherProfiles AngularFiniteProjector
open AngularCanonicalCoefficient
local notation "Eis" => ActualEisensteinCubic.O

def physicalProjector (Φ : Eis →* ℂ) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (v : ℝ) : ℂ :=
  ∑ h : Eis ⧸ Ideal.span {c},
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c) h *
      barProfile cubicSourceConjugateFunction (n+1) (thetaFourierTranslation c h) v

theorem physicalProjector_fourier (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q) (v : ℝ) (hv : 0 < v) :
    physicalProjector Φ n c hc v = ∑' h : Eis,
      (-2 * Real.pi * Complex.I * star (cuspFrequency h)) ^ (n+1) *
        fixedThetaTwist Φ h * star (sourceResidualFourierCoefficient h) *
          (v : ℂ) * schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  let weight : (Eis ⧸ Ideal.span {c}) → ℂ :=
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Φ c)
  let term : (Eis ⧸ Ideal.span {c}) → NonzeroFrequency → ℂ := fun a h =>
    conjugateBarCoefficient sourceBesselCoefficients (n+1) (thetaFourierTranslation c a) h *
      (v : ℂ) * schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)
  have hsum (a : Eis ⧸ Ideal.span {c}) : Summable (fun h => weight a * term a h) :=
    (conjugate_fourier_summable sourceBesselCoefficients (n+1)
      (thetaFourierTranslation c a) v hv).mul_left (weight a)
  calc
    _ = ∑ a : Eis ⧸ Ideal.span {c}, ∑' h : NonzeroFrequency, weight a * term a h := by
      unfold physicalProjector
      apply Finset.sum_congr rfl
      intro a ha
      rw [source_conjugate_barProfile_fourier n _ v hv, ← tsum_mul_left]
    _ = ∑' h : NonzeroFrequency, ∑ a : Eis ⧸ Ideal.span {c}, weight a * term a h :=
      (Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => hsum a)).symm
    _ = ∑' h : NonzeroFrequency,
        (-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n+1) *
          fixedThetaTwist Φ h.val *
            star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
              schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
      apply tsum_congr
      intro h
      have he (a : Eis ⧸ Ideal.span {c}) : weight a * term a h =
          (weight a * ShortDraftTrace.breveE (-cuspFrequency h.val * thetaFourierTranslation c a)) *
            (-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n+1) *
              star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
                schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
        simp only [term, conjugateBarCoefficient, derivativeScalar, sourceBesselCoefficients]
        ring
      simp_rw [he]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      have hi := thetaFourierTranslation_inversion c hc
        (fixedThetaQuotient Φ c) h.val
      change (∑ a, weight a * ShortDraftTrace.breveE
        (-cuspFrequency h.val * thetaFourierTranslation c a)) = _ at hi
      rw [hi, fixedThetaQuotient_mk Φ Q
        hperiod c hcQ]
      ring
    _ = _ := by
      symm
      rw [← tsum_subtype_eq_of_support_subset (s := {h : Eis | h ≠ 0}) (by
        intro h hh hz
        subst h
        exact hh (by simp [cuspFrequency]))]
      rfl

/-- Actual projected profile, reindexed onto the pinned squarefree/cube
primary pairs and identified with the actual angular completed coefficient. -/
theorem physicalProjector_primary_pairs (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ)
    (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q) (v : ℝ) (hv : 0 < v) :
    physicalProjector Φ n c hc v =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      ∑' p : ({I : Ideal Eis // Squarefree I ∧ primaryGenerator I ≠ 0} ×
        {J : Ideal Eis // primaryGenerator J ≠ 0}),
        completedMellinCoefficient (negativeAngularTwist Φ n) (primaryCubePairToMellinIndex p) *
          ((completedMellinLength (primaryCubePairToMellinIndex p) : ℂ) *
            (Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p)) : ℂ) ^ n) *
          (v : ℂ) * schlafliBesselK (1/3)
            (4 * Real.pi * thetaBesselScale *
              Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p)) * v) := by
  rw [physicalProjector_fourier Φ Q hperiod n c hc hcQ v hv]
  let w : Eis → ℂ := fun h => (-2 * Real.pi * Complex.I * star (cuspFrequency h)) ^ (n+1) *
    fixedThetaTwist Φ h * (v : ℂ) *
      schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h‖ * v)
  have hw : ∀ h : Eis, w h ≠ 0 → ActualEisensteinCubic.lambda ^ 2 ∣ h - 1 := by
    intro h hwh
    by_contra hh
    exact hwh (by simp only [w, fixedThetaTwist_not_primary _ h hh, mul_zero, zero_mul])
  calc
    _ = ∑' h : Eis, w h * star (sourceResidualFourierCoefficient h) := by
      apply tsum_congr
      intro h
      dsimp only [w]
      ring
    _ = ∑' p : ({I : Ideal Eis // Squarefree I ∧ primaryGenerator I ≠ 0} ×
        {J : Ideal Eis // primaryGenerator J ≠ 0}),
        w (primaryGenerator p.1.val * (primaryGenerator p.2.val) ^ 3) *
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val * (primaryGenerator p.2.val) ^ 3)) :=
      sourceFourier_tsum_primary_pairs w hw
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      let ip := primaryCubePairToMellinIndex p
      have he := thetaPair_negativeAngularTwist Φ n ip.1 ip.2
        p.1.property.2 p.2.property p.1.property.1
      have hn := thetaPair_frequency_norm ip.1 ip.2 p.1.property.2 p.2.property
      change (-2 * Real.pi * Complex.I *
          star (cuspFrequency (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3))) ^ (n+1) *
        fixedThetaTwist Φ
          (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3) * (v : ℂ) *
          schlafliBesselK (1/3)
            (4 * Real.pi * ‖cuspFrequency (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3)‖ * v) *
        star (sourceResidualFourierCoefficient
          (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3)) =
        (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
          (completedMellinCoefficient (negativeAngularTwist Φ n) ip *
            ((completedMellinLength ip : ℂ) * (Real.sqrt (completedMellinLength ip) : ℂ) ^ n) *
            (v : ℂ) * schlafliBesselK (1/3)
              (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength ip) * v))
      rw [hn, show 4 * Real.pi * (thetaBesselScale * Real.sqrt (completedMellinLength ip)) * v =
        4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength ip) * v by ring]
      calc
        _ = ((-2 * Real.pi * Complex.I *
            star (cuspFrequency (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3))) ^ (n+1) *
          fixedThetaTwist Φ
            (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3) *
          star (sourceResidualFourierCoefficient
            (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3))) *
          (v : ℂ) * schlafliBesselK (1/3)
            (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength ip) * v) := by ring
        _ = _ := by rw [he]; ring

/-- The same actual profile equality over all completed Mellin indices;
the original support theorem supplies the zero coefficients off support. -/
theorem physicalProjector_completed_indices (Φ : Eis →* ℂ) (Q : Ideal Eis)
    (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ) (n : ℕ)
    (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q) (v : ℝ) (hv : 0 < v) :
    physicalProjector Φ n c hc v =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      ∑' p : CompletedMellinIndex,
        completedMellinCoefficient (negativeAngularTwist Φ n) p *
          ((completedMellinLength p : ℂ) * (Real.sqrt (completedMellinLength p) : ℂ) ^ n) *
          (v : ℂ) * schlafliBesselK (1/3)
            (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength p) * v) := by
  rw [physicalProjector_primary_pairs Φ Q hperiod n c hc hcQ v hv]
  congr 1
  simpa only [mul_assoc] using
    (completedMellinCoefficient_tsum_primary_pairs (negativeAngularTwist Φ n)
      (fun p => ((completedMellinLength p : ℂ) * (Real.sqrt (completedMellinLength p) : ℂ) ^ n) *
        (v : ℂ) * schlafliBesselK (1/3)
          (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength p) * v))).symm


#print axioms physicalProjector_completed_indices
end OAI.CubicEisenstein.AngularCanonicalProjector
