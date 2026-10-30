import AngularMarkedReflection

/-! All-order cusp congruence. Equality of the actual finite additive
multipliers implies equality of the normalized reflected kernel sums.
Both Fourier and integral interchanges use proved convergence. -/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularCuspCongruence
open CompletedGauss ConcreteTraceCRT SevenEighths.InverseMoment
open AngularHigherProfiles AngularBesselDerivatives AngularBesselClosure AngularProfileDirichlet
open AngularFiniteProjector AngularProjectedReflection AngularShiftedBesselReflection
open AngularPhysicalSmoothedReflection AngularCanonicalCoefficient AngularMarkedReflection
local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

def weightedProfile {ι : Type*} [Fintype ι] (n : ℕ)
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (v : ℝ) : ℂ :=
  ∑ i, w i * barProfile cubicSourceConjugateFunction (n+1) (d i).point v

theorem weightedProfile_fourier {ι : Type*} [Fintype ι] (n : ℕ)
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (v : ℝ) (hv : 0 < v) :
    weightedProfile n d w v = ∑' h : NonzeroFrequency,
      (∑ i, w i * ShortDraftTrace.breveE (-cuspFrequency h.val * (d i).point)) *
        ((-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n+1) *
          star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
          schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)) := by
  let term : ι → NonzeroFrequency → ℂ := fun i h =>
    conjugateBarCoefficient sourceBesselCoefficients (n+1) (d i).point h *
      (v : ℂ) * schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)
  have hsum (i : ι) : Summable (fun h => w i * term i h) :=
    (conjugate_fourier_summable sourceBesselCoefficients (n+1) (d i).point v hv).mul_left (w i)
  calc
    _ = ∑ i, ∑' h : NonzeroFrequency, w i * term i h := by
      unfold weightedProfile
      apply Finset.sum_congr rfl
      intro i hi
      rw [source_conjugate_barProfile_fourier n _ v hv, ← tsum_mul_left]
    _ = ∑' h : NonzeroFrequency, ∑ i, w i * term i h :=
      (Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) => hsum i)).symm
    _ = _ := by
      apply tsum_congr
      intro h
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [term, conjugateBarCoefficient, derivativeScalar, sourceBesselCoefficients]
      ring

theorem weightedProfile_mellin {ι : Type*} [Fintype ι] (n : ℕ)
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (s : ℂ) :
    mellin (weightedProfile n d w) s =
      ∑ i, w i * mellin (barProfile cubicSourceConjugateFunction (n+1) (d i).point) s := by
  have hi (i : ι) : IntegrableOn
      (fun v : ℝ => (v : ℂ) ^ (s-1) *
        (w i * barProfile cubicSourceConjugateFunction (n+1) (d i).point v)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using
      ((datum_mellin_entire n (d i)).1 s).const_smul (w i)
  unfold mellin weightedProfile
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [mellin, smul_eq_mul] using mellin_const_smul
    (barProfile cubicSourceConjugateFunction (n+1) (d i).point) s (w i)

theorem weightedProfile_smoothing {ι : Type*} [Fintype ι] (n : ℕ)
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (s : ℂ) :
    smoothingIntegrand n (weightedProfile n d w) thetaBesselScale V X s =
      ∑ i, w i * smoothingIntegrand n
        (barProfile cubicSourceConjugateFunction (n+1) (d i).point) thetaBesselScale V X s := by
  unfold smoothingIntegrand continuedDirichlet
  rw [weightedProfile_mellin]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weightedProfile_smoothing_integral {ι : Type*} [Fintype ι] (n : ℕ)
    (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (V : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support V ⊆ Icc lo hi) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * datumSmoothedDual n (d i) V X) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        smoothingIntegrand n (weightedProfile n d w) thetaBesselScale V X
          ((-1 : ℂ) + t * Complex.I) := by
  simp_rw [weightedProfile_smoothing]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (datum_smoothing_integrable n (d i) V lo hi hlo hsupp hV X hX).const_mul (w i)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, ← datum_smoothing_integral n (d i) V lo _ hlo hsupp hV X hX]
  ring

theorem cusp_normalized_sum_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (e : κ → SourceCuspDatum) (z : κ → ℂ)
    (hmult : ∀ a : Eis,
      (∑ i, w i * ShortDraftTrace.breveE (-cuspFrequency a * (d i).point)) =
        ∑ k, z k * ShortDraftTrace.breveE (-cuspFrequency a * (e k).point))
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * normalizedDual n (d i) W X) =
      ∑ k, z k * normalizedDual n (e k) W X := by
  have hprofile (v : ℝ) (hv : 0 < v) : weightedProfile n d w v = weightedProfile n e z v := by
    rw [weightedProfile_fourier n d w v hv, weightedProfile_fourier n e z v hv]
    simp_rw [hmult]
  have hm (s : ℂ) : mellin (weightedProfile n d w) s = mellin (weightedProfile n e z) s :=
    mellin_eq_of_positive_eq _ _ hprofile s
  have hVs := Vstar_support W lo hi hsupp
  have hV := Vstar_contDiff W lo hi hlo hsupp hW
  simp only [normalizedDual, ← mul_div_assoc, ← Finset.sum_div]
  rw [weightedProfile_smoothing_integral n d w (Vstar W) lo hi hlo hVs hV X hX,
    weightedProfile_smoothing_integral n e z (Vstar W) lo hi hlo hVs hV X hX]
  simp only [smoothingIntegrand, continuedDirichlet, hm]

theorem marked_of_cusp_multiplier {ι κ : Type*} [Fintype κ]
    (p : ι → Eis) (S : Finset ι) (hp : ∀ i ∈ S, Prime (p i))
    (Φ : Eis →* ℂ) (hΦ : ∀ x, ‖Φ x‖ ≤ 1) (n : ℕ)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (d : κ → SourceCuspDatum) (w : κ → ℂ)
    (hmult : ∀ a : Eis, (∑ k, w k * ShortDraftTrace.breveE (-cuspFrequency a * (d k).point)) =
      markedThetaQuotient p S Φ c (Ideal.Quotient.mk _ a))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (negativeAngularTwist Φ n) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ k, w k * normalizedDual n (d k) W X := by
  rw [marked_canonical_reflection p S hp Φ hΦ n Q hperiod c hc hcQ
    W hWcompact lo hi hlo hsupp hW X hX]
  apply cusp_normalized_sum_congr n (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Φ c)) d w
    ?_ W lo hi hlo hsupp hW X hX
  intro a
  simp_rw [finiteTwistCusp_point]
  rw [thetaFourierTranslation_inversion c hc, hmult]

#print axioms cusp_normalized_sum_congr
#print axioms marked_of_cusp_multiplier
end OAI.CubicEisenstein.AngularCuspCongruence
