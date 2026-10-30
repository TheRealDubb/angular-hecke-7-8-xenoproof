import AngularMixedReflection

/-! Chosen controlled data for the exact marked angular reflected series.
Adapted from the pinned original MarkedChosenSource and MarkedChosenDual.
This keeps the finite local sums and active/inactive masks before all estimates. -/

noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularChosenReflection
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open SevenEighths.InverseMoment SevenEighths.InverseReflectedPhase
open AngularCanonicalCoefficient AngularMarkedReflection AngularActiveReflection AngularMixedReflection
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] (n : ℕ) (P : PrimeFamily ι)

theorem marked_source_of_controlled
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (negativeAngularTwist φ n * unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    ∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      normalizedDual n (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t) W X := by
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
    C call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX

lemma fixed_active_sum_eq_mixed_of_controlled
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      normalizedDual n (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t) W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        angularMixedSmoothed n (C h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  simp only [angularMixedSmoothed,Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  have hw : fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v =
      fullLocalFourierWeight (fun i : A => P.generator_ne_zero i.val)
        (mixedPrimeFunction (fun i : A => P.generator i.val) (fun i => P.generator_good i.val)
          (fun i => j i.val) (activeMarks A S)) v := rfl
  rw [hw]
  dsimp only [activeStratumDatum]
  ring

theorem marked_reflected_source_of_controlled
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (negativeAngularTwist φ n * unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        angularMixedReflected n (C h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [marked_source_of_controlled n P hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN C
    W hWcompact lo hi hlo hsupp hW X hX,
    fixed_active_sum_eq_mixed_of_controlled n P hP j S φ c hc G N hN C W X]
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply angularMixed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX

#print axioms marked_reflected_source_of_controlled
end OAI.CubicEisenstein.AngularChosenReflection
