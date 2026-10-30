import AngularRawTail

/-! Natural zero extensions and the actual angular coefficients in the tail.
This is a bound on the literal reflected tail; the principal terminal hybrid
norm and the canonical moment estimate are separate obligations. -/
namespace OAI.CubicEisenstein.AngularRawCoefficient
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CompletedGauss CompletedDyadic SevenEighths.InverseMoment SevenEighths.Angular
open SevenEighths.InverseReflectedPhase AngularRawTail AngularPhaseSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def angularLiteralRawCoefficient (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  literalRawCoefficient G D s hc j S u m n b * alpha (fixedCuspArrayIndex u m n b) ^ order

lemma angularLiteralRawCoefficient_norm (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1)
    (hchar : ∀ i, ringChar (Eis ⧸ G.ideal i) ≠ 2) (j : ι → ℕ) (hj : ∀ i, j i < 6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖angularLiteralRawCoefficient order G D s hc j S u m n.val b.val‖ ≤ (Ideal.absNorm (∏ i, G.ideal i) : ℝ) := by
  exact (angular_column_product_bound _ _ _).trans
    (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u m n b)

theorem angular_literal_reflected_raw_tail (order : ℕ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
      Summable (fun x => ‖if cut x then angularRawDualKernelTerm order V scale 1 completedRamifiedStep
        (angularLiteralRawCoefficient order G D s hc j S u) x else 0‖) ∧
      ‖∑' x, if cut x then angularRawDualKernelTerm order V scale 1 completedRamifiedStep
        (angularLiteralRawCoefficient order G D s hc j S u) x else 0‖≤
      C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := angular_raw_kernel_tail order a₀ b₀ completedRamifiedStep ha₀ completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (angularLiteralRawCoefficient order G D s hc j S u) (angularLiteralRawCoefficient_norm order G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh

#print axioms angular_literal_reflected_raw_tail
end
end OAI.CubicEisenstein.AngularRawCoefficient
