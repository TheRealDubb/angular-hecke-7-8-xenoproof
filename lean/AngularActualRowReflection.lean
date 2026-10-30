import AngularActiveReflection
import OAI.NumberTheory.DirichletL.Reflection.MarkedActualSource

/-! The actual canonical row retains its masks and finite local factors.
Angular twisting commutes with the row factorization. The marked source
is an equality before any norm estimates or projection of row parameters. -/

noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularActualRowReflection
open CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseReflectedPhase
open AngularCanonicalCoefficient AngularMarkedReflection AngularActiveReflection
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem rowTwist_angular (Φ : Eis →* ℂ) (n : ℕ) (m f z : Eis) :
    rowTwist (negativeAngularTwist Φ n) m f z = negativeAngularTwist (rowTwist Φ m f z) n := by
  simp only [rowTwist, negativeAngularTwist_mul]

theorem fixedFactor_angular {m f z : Eis} (D : GoodMaskRowData m f z)
    (Φ : Eis →* ℂ) (Q : Ideal Eis) (n : ℕ) :
    D.fixedFactor (negativeAngularTwist Φ n) Q = negativeAngularTwist (D.fixedFactor Φ Q) n := by
  simp only [GoodMaskRowData.fixedFactor, negativeAngularTwist_mul]

theorem marked_family_source {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ a, ‖φ a‖≤1) (n : ℕ)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (negativeAngularTwist φ n * unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    ∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      normalizedDual n (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t) W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact marked_angular_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm n Q hφperiod c hc hcQ G N hN
    (P.activeControlled hP c G N hN hNp) call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX

def markedAngularCuspSource {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (n : ℕ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  ∑ t : FixedActiveCuspIndex c P.generator,
    fixedActiveFunctionWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
    normalizedDual n (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
      (P.activeControlled hP c G N hN hNp) t) W X

theorem actual_marked_angular_row_source {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (Ψ : Eis→*ℂ) (n : ℕ) (Q : Ideal Eis) (hQ : Q≠0)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm : ∀ n, ‖Ψ n‖≤1)
    (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}), ∀ i, S.ideal i≠P.val.val)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((markedRowFamily D S Q).ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist (negativeAngularTwist Ψ n) m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    markedAngularCuspSource (markedRowFamily D S Q)
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) n c hc G N hN hNp W X := by
  have hQ0 : Q * Ideal.span {(72 : Eis)} ≠ 0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    norm_num
  have hrow := actual_marked_row_eq_joined D S (negativeAngularTwist Ψ n) Q hmLam hm2 W X
  dsimp only at hrow
  rw [fixedFactor_angular] at hrow
  exact hrow.trans
    (marked_family_source (markedRowFamily D S Q)
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm)
      n (Q*Ideal.span {(72:Eis)}) hQ0 (D.fixedFactor_periodic Ψ Q hΨ) c hc hcQ G N hN hNp
      W hWcompact lo hi hlo hsupp hW X hX)

#print axioms actual_marked_angular_row_source

end OAI.CubicEisenstein.AngularActualRowReflection
