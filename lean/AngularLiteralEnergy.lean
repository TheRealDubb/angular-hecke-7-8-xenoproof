import AngularShellRows
import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalizedUniformDegree

/-! Literal angular dyadic row and its normalized sector estimate. The
geometric phase is retained inside the slot sum. Exact shell identities connect
it to the physical angular cell before using the quantitative energy bound. -/
namespace OAI.CubicEisenstein.AngularLiteralEnergy
open scoped Classical BigOperators ContDiff
open SevenEighths ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
open InverseReflectedPhase AngularControlledScalar AngularPhysicalCell
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
section
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def angularLiteralDyadicRow (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    shapeOrderPhase s (c * ∏ j, (F.reflected K hK (S P.val.val)).generator j)^order*
    AngularFullDyadic.angularLiteralDyadicBlock order (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) X u i

theorem angularLiteralDyadicRow_eq_physical (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hprod : ∀ P∈Pset, (∏ j,(S P).ideal j)=P)
    (hPr : ∀ P∈Pset, QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) :
    angularLiteralDyadicRow order F K hK S jF Pset D s hc u i W θ X r aw=
      physicalAngularKernelRow order F K hK S jF Pset (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
        D s hc u i.1 (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
        W θ X r aw (fun _ _ => 1) := by
  unfold angularLiteralDyadicRow physicalAngularKernelRow CoprimeSourceIndex
  simp only [Fintype.sum_prod_type,mul_one]
  apply Finset.sum_congr rfl
  intro P hP
  have hp : QP/2≤(Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ) ∧
      (Ideal.absNorm (∏ j,(S P.val.val).ideal j):ℝ)≤QP := by
    rw [hprod P.val.val P.val.property]
    exact hPr P.val.val P.val.property
  rw [AngularShellRows.literalDyadicBlock_eq_filtered_source order F K hK (S P.val.val) jF (D P.val P.property)
    s hc u i QK QP hQK hQP hKr hp W θ X]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  unfold AngularShellRows.angularShellTerm
  ring
end

theorem sector_normalized_angular_literal_energy (order : ℕ)
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (η : ℝ) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c∣N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f,jF f<6) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) F rows Pset S hrows s hc),
      (∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ j,IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal j)) →
      (∀ P∈Pset,∀ j,ringChar (Eis⧸(F.sum (S P)).ideal j)≠2) →
    ∀ (u : Eisˣ) (i : ℕ×ℕ×ℕ) (T θ QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<T → 1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      (∑ K : rows,‖angularLiteralDyadicRow order F K.val (hrows K.val K.property) S jF Pset
        (E.completion K) s hc u i W θ T r aw‖^2)≤
      ((branches.card:ℝ)*∑ e∈branches,
        (Real.exp (Real.log 2/2+Real.log 2))^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z QK)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z (QP/2))
            (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1)))
            (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2)))
            (InverseTerminalWidths.ramifiedWidth Z i.1)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z (QP/2)) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z QK+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+Real.logb Z (QP/2))+η/2))*
        (C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := AngularNormalizedSector.sector_normalized_angular_cell_energy order
    ε hε lo hi hlo
    (fun _ => completedShellWindow) (fun _ => Real.log 2)
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ => completedShellWindow_norm)
    (fun _ => completedShellWindow_support) W hWs hW 1 (1/2) 1 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,Z₀,hC₀,hC,hZ₀,henergy⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode) s hc
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ F jF hN hbase hac hF hNF hcharF hj rows Pset S hrows E
    hrowcop hprod hScop hSN hSchar u i T θ QK QP r aw hT hQK hQP hKr hPr hr haw
  have hkp : 0<QK := lt_of_lt_of_le zero_lt_one hQK
  have hpp : 0<QP := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hQP
  have hp : ∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*(QP/2) := by
    intro P hP
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hPr P hP
  have hh := henergy Z hZ QK ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) (QP/2)
    hQK (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (by linarith)
    F jF hN hbase hac hF hNF hcharF hj u i.1 T θ QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    hT hkp hpp (by positivity) (by positivity) (by ring) (by ring) (by ring) (by ring)
    rows (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) Pset S
    (fun K hK => ⟨hrows K hK,(hKr K hK).2⟩) E r aw (fun _ _ => 1)
    hrowcop hprod hScop hSN hSchar
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩)
    hp hr haw (fun _ _ => by simp)
  dsimp only at hh ⊢
  have he : (∑ K : rows,‖angularLiteralDyadicRow order F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i W θ T r aw‖^2)=
      ∑ K : rows,‖physicalAngularKernelRow order F K.val (hrows K.val K.property) S jF Pset
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) (E.completion K) s hc u i.1
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ T r aw (fun _ _ => 1)‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    rw [angularLiteralDyadicRow_eq_physical order F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i QK QP hkp hpp (hKr K.val K.property) hprod
      (fun P hP => (hPr P hP).2) W θ T r aw]
  rw [he]
  simpa only [Real.sqrt_one,mul_one] using hh

#print axioms angularLiteralDyadicRow_eq_physical
#print axioms sector_normalized_angular_literal_energy
end
end OAI.CubicEisenstein.AngularLiteralEnergy
