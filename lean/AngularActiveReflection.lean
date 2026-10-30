import AngularCuspCongruence

/-! Actual marked angular sum equals its active/inactive cusp expansion.
The original finite multipliers, masks, and controlled matrices are retained.
Only the finite factor phi is assumed periodic. No absolute values are taken. -/

noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularActiveReflection
open CompletedGauss CanonicalRowCompletion SevenEighths.InverseMoment
open AngularCanonicalCoefficient AngularMarkedReflection AngularCuspCongruence
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance angularActiveQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem marked_angular_active_strata {ι : Type*} [Fintype ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : Eis →* ℂ) (hφnorm : ∀ a, ‖φ a‖ ≤ 1) (n : ℕ)
    (Q : Ideal Eis) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : Eis) (hcall : call ≠ 0) [Fintype (Eis ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : Eis)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (negativeAngularTwist φ n * unmarkedSexticTwist p hg j S) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          normalizedDual n (fixedActiveCuspDatum p hp hprimary c G N hN D t) W X := by
  rw [← negativeAngularTwist_mul]
  have hnorm (n : Eis) : ‖(φ * unmarkedSexticTwist p hg j S) n‖ ≤ 1 := by
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n)).trans
      (unmarkedSexticTwist_norm p hg j S n)
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_left hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_right hxy)]
  apply marked_of_cusp_multiplier p S (fun i _ => hprime i) _ hnorm n _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring

#print axioms marked_angular_active_strata
end OAI.CubicEisenstein.AngularActiveReflection
