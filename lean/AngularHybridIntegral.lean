import AngularPhysicalHybrid

/-! Common-measure energy contraction for the separated physical angular
weights. The density is explicit and must be integrable; its actual kernel
construction and quantitative moments are proved in AngularKernelSourceUniform.
This theorem does not assert the canonical moment or discharge its row counts. -/
namespace OAI.CubicEisenstein.AngularHybridIntegral
open scoped Classical BigOperators
open MeasureTheory SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
open InverseReflectedPhase AngularHybridEnergy
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {Ω : Type*} [MeasurableSpace Ω] {N a c : Eis} {mode : Bool}

theorem angular_integrated_summed_reflected_energy (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (angularIdealWeight order (r t))
        (angularIdealWeight order (aw t)) (angularDualWeight order u m (w t)) u m Pset nset bset K) ∂μ‖^2) ≤
      ‖scalar‖^2*((Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := integrated_summed_actual_reflected_energy_type_uniform
    (Ω := Ω) (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S μ density scalar
    (fun t => angularIdealWeight order (r t)) (fun t => angularIdealWeight order (aw t))
    (fun t => angularDualWeight order u m (w t))
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity
    (fun K hK => (hrM K hK).mul_const _)
    (fun P hP => (hawM P hP).mul_const _)
    (fun n hn b hb => (hwM n hn b hb).mul_const _)
    (fun t K hK => (angularIdealWeight_norm_le order (r t) K).trans (hr t K hK))
    (fun t P hP => (angularIdealWeight_norm_le order (aw t) P).trans (haw t P hP))
    (fun t n b => (angularDualWeight_norm_le order u m (w t) n b).trans (hw t n b))

#print axioms angular_integrated_summed_reflected_energy
end
end OAI.CubicEisenstein.AngularHybridIntegral
