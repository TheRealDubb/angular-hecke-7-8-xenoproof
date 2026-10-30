import AngularPhysicalKernel

/-! A quantitative bound for the literal finite angular cell. The geometric
phase and dual angular frequency occur inside its defining sum. Equality to
separated weights is proved before norms; the fixed phase has norm one.
The outer fixed radial/cusp scalar and aggregation over cells are not part
of this cell theorem and remain explicit downstream obligations. -/
namespace OAI.CubicEisenstein.AngularPhysicalCell
open scoped Classical BigOperators ContDiff
open MeasureTheory SevenEighths ActualEisensteinCubic CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseKernelSourceUniform
open AngularPhaseSeparation AngularControlledScalar AngularHybridEnergy AngularPhysicalHybrid
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def physicalAngularKernelRow (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4 → ℝ → ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ → ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis → ℂ) (w₀ : Ideal Eis → Ideal Eis → ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K * aw₀ x.1.val.val * w₀ x.2.1.val x.2.2.val) *
      AngularPhysicalKernel.actualKernelSourceTerm order F K hK (S x.1.val.val) jF
        (D x.1.val x.1.property) s hc u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X *
      shapeOrderPhase s (c * ∏ i, (F.reflected K hK (S x.1.val.val)).generator i) ^ order *
      Angular.alpha (fixedCuspArrayIndex u m x.2.1.val x.2.2.val) ^ order

theorem physicalAngularKernelRow_separate (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i) = P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4 → ℝ → ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ → ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis → ℂ) (w₀ : Ideal Eis → Ideal Eis → ℂ) :
    physicalAngularKernelRow order F K hK S jF Pset nset bset D s hc u m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
      shapeOrderPhase s (c * ∏ i, F.generator i) ^ order *
        AngularPhysicalKernel.weightedFinitePhysicalKernelRow order F K hK S jF Pset nset bset D s hc u m windows
          QK QP Qn Qb W θ X (angularIdealWeight order r₀) (angularIdealWeight order aw₀)
          (angularDualWeight order u m w₀) := by
  unfold physicalAngularKernelRow AngularPhysicalKernel.weightedFinitePhysicalKernelRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [reflected_shape_phase, hprod x.1.val.val x.1.val.property]
  unfold angularIdealWeight angularDualWeight
  ring

theorem physical_angular_cell_energy (order : ℕ)
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C₀ C : ℝ), 0≤C₀ ∧ 0<C ∧
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
      let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R
      (∑ K : rows, ‖physicalAngularKernelRow order F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      scalar^2*((Fintype.card (φ→Fin 3):ℝ)*∑ e : φ→Fin 3,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,C₀,C,hC₀,hC,he⟩ := AngularPhysicalKernel.finite_physical_source_energy order
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows W hWsupport hW
  refine ⟨degree,C₀,C,hC₀,hC,?_⟩
  intro X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  have hh := he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D
    (angularIdealWeight order r₀) (angularIdealWeight order aw₀) (angularDualWeight order u m w₀)
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA
    (fun K hK => (angularIdealWeight_norm_le order r₀ K).trans (hr₀ K hK))
    (fun P hP => (angularIdealWeight_norm_le order aw₀ P).trans (haw₀ P hP))
    (fun n b => (angularDualWeight_norm_le order u m w₀ n b).trans (hw₀ n b))
  have hphase : ‖shapeOrderPhase s (c * ∏ i, F.generator i) ^ order‖ = 1 := by
    rw [norm_pow, shapeOrderPhase_norm s _
      (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i))), one_pow]
  apply le_trans (le_of_eq (Finset.sum_congr rfl (fun K _ => ?_))) hh
  rw [physicalAngularKernelRow_separate order F K.val (hrows K.val K.property).1 S jF
    Pset nset bset hproducts, norm_mul, hphase, one_mul]

#print axioms physicalAngularKernelRow_separate
#print axioms physical_angular_cell_energy
end
end OAI.CubicEisenstein.AngularPhysicalCell
