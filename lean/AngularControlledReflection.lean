import AngularFixedCuspSeries

/-! All-order physical controlled-stratum reflection with the actual
mixed local brackets and complete squarefree/cube frequency index. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularControlledScalar

open CompletedGauss CompletedDyadic CubicKubota ConcreteTraceCRT ActualEisensteinCubic
open SevenEighths.InverseMoment AngularPhysicalSmoothedReflection ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance reflectionQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem controlled_smoothed_reflection {ι : Type*} [Fintype ι]
    {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (n : ℕ) (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hVs : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0 < X) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
        (datumSmoothedDual n (D.datum hN hr hbase s hp hc0 v) V X / initialScalar n)) =
    ∑' q : ThetaFullIndex, fixedSeriesTerm n s (c0 * ∏ i, p i) V X q *
      (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency q))) *
      ∏ i, mixedActiveBracket hp hg j S D i
        (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency q)) := by
  have hprod : c0 * ∏ i, p i ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have he := sum_fixedCusp_normalized_reflection n s (D.sourceGamma hN hr hbase)
    (c0 * ∏ i, p i) hprod (fun v => by rw [D.sourceGamma_mul, D.denominator])
    (fullLocalFourierWeight hp (mixedPrimeFunction p hg j S)) V a b ha hVs hV X hX
  change (∑ v, fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
    (datumSmoothedDual n (s.datum (D.sourceGamma hN hr hbase v) _) V X /
      initialScalar n)) = _
  rw [he]
  apply tsum_congr
  intro q
  simp only [D.sourceGamma_character, D.sourceGamma_mul, map_mul]
  rw [controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S]
  ring

#print axioms controlled_smoothed_reflection

end OAI.CubicEisenstein.AngularControlledScalar
