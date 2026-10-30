import AngularActualRowReflection
import OAI.NumberTheory.DirichletL.Reflection.MarkedChosenDual

/-! Physical mixed-stratum value with its exact normalized angular kernel.
No row-dependent absolute-value loss is introduced by this conversion. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups
namespace OAI.CubicEisenstein.AngularMixedReflection
open CompletedGauss ConcreteTraceCRT SevenEighths.InverseMoment
open AngularControlledScalar AngularMarkedReflection ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance angularMixedQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def angularMixedSmoothed (n : ℕ) (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
    fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      normalizedDual n (D.datum hN hr hbase s hp hc0 v) W X

def angularMixedReflected (n : ℕ) (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' q : ThetaFullIndex, fixedSeriesTerm n s (c0 * ∏ i, p i) (Vstar W) X q *
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency q))) *
    ∏ i, mixedActiveBracket hp hg j S D i
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency q))

theorem angularMixed_eq_reflected (n : ℕ) (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    angularMixedSmoothed n D hN hr hbase s hp hc0 hg j S W X =
      angularMixedReflected n D s hp hc0 hg j S W X := by
  exact controlled_smoothed_reflection D hN hr hbase hp hc0 hcop hg hc j hj S s n
    (Vstar W) lo hi hlo (Vstar_support W lo hi hsupp)
    (Vstar_contDiff W lo hi hlo hsupp hW) X hX

#print axioms angularMixed_eq_reflected
end OAI.CubicEisenstein.AngularMixedReflection
