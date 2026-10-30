import AngularKernelSeparation
import OAI.NumberTheory.DirichletL.Reflection.UniformSieve

/-! The original quadratic/cubic energy estimate applied to the separated
angular row, slot and dual weights. Its bounds retain exactly the original
extracted scales and branch multiplicities. This is the arithmetic norm
step, not the complete canonical moment theorem. -/
namespace OAI.CubicEisenstein.AngularHybridEnergy
open scoped Classical BigOperators
open SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseMoment
open SevenEighths.InverseReflectedPhase SevenEighths.Angular AngularPhaseSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {N a c : Eis} {mode : Bool}

lemma denominatorPhase_norm_le_one (z : Eis) : ‖denominatorPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [denominatorPhase, hz]
  · exact (denominatorPhase_norm z hz).le

def angularIdealWeight (order : ℕ) (w : Ideal Eis → ℂ) (I : Ideal Eis) : ℂ :=
  w I * denominatorPhase (primaryGenerator I) ^ order

def angularDualWeight (order : ℕ) (u : Eisˣ) (m : ℕ)
    (w : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  w n b * alpha (fixedCuspArrayIndex u m n b) ^ order

lemma angularIdealWeight_norm_le (order : ℕ) (w : Ideal Eis → ℂ) (I : Ideal Eis) :
    ‖angularIdealWeight order w I‖ ≤ ‖w I‖ := by
  rw [angularIdealWeight, norm_mul, norm_pow]
  simpa using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg _) (denominatorPhase_norm_le_one _) :
      ‖denominatorPhase (primaryGenerator I)‖ ^ order ≤ 1) (norm_nonneg (w I))

lemma angularDualWeight_norm_le (order : ℕ) (u : Eisˣ) (m : ℕ)
    (w : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) :
    ‖angularDualWeight order u m w n b‖ ≤ ‖w n b‖ :=
  angular_column_product_bound _ _ _

theorem angular_weighted_reflected_branch_energy (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
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
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (angularIdealWeight order r)
          (angularIdealWeight order aw) (angularDualWeight order u m w) u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy_type_uniform
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S (angularIdealWeight order r)
    (angularIdealWeight order aw) (angularDualWeight order u m w)
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP
    (fun K hK => (angularIdealWeight_norm_le order r K).trans (hr K hK))
    (fun P hP => (angularIdealWeight_norm_le order aw P).trans (haw P hP))
    (fun n b => (angularDualWeight_norm_le order u m w n b).trans (hw n b))

theorem angular_summed_reflected_energy (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
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
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (angularIdealWeight order r)
          (angularIdealWeight order aw) (angularDualWeight order u m w) u m Pset nset bset K‖^2) ≤
      (Fintype.card (φ→Fin 3):ℝ) * ∑ e : φ→Fin 3,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := summed_actual_weighted_reflected_energy_type_uniform
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S (angularIdealWeight order r)
    (angularIdealWeight order aw) (angularDualWeight order u m w)
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP
    (fun K hK => (angularIdealWeight_norm_le order r K).trans (hr K hK))
    (fun P hP => (angularIdealWeight_norm_le order aw P).trans (haw P hP))
    (fun n b => (angularDualWeight_norm_le order u m w n b).trans (hw n b))


#print axioms angular_weighted_reflected_branch_energy
#print axioms angular_summed_reflected_energy
end
end OAI.CubicEisenstein.AngularHybridEnergy
