import AngularControlledPhase

/-! Exact preservation of the original mixed local bracket after insertion
of the actual all-order geometric scalar. This is the finite cancellation
step; it does not assert a smoothed-series identity or a moment estimate. -/

noncomputable section
open scoped Classical BigOperators MatrixGroups

namespace OAI.CubicEisenstein.AngularControlledScalar

open CubicKubota ConcreteTraceCRT ActualEisensteinCubic ShortDraftCusp
open SevenEighths.InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance quotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem controlled_normalized_multiplier {ι : Type*} [Fintype ι]
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
    (n : ℕ) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
        normalizedScalar n (D.datum hN hr hbase s hp hc0 v) *
          ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) *
            (eisEmbedding x / eisLam ^ 4)) /
              (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
      (s.stratumShapeFactor (c0 * ∏ i, p i) *
        (sourceCuspScale s.index : ℂ) ^ 2 / thetaDerivativeScalar *
          shapeOrderPhase s (c0 * ∏ i, p i) ^ n) *
      (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
        ∏ i, mixedActiveBracket hp hg j S D i x := by
  let C : ℂ := s.stratumShapeFactor (c0 * ∏ i, p i) *
    (sourceCuspScale s.index : ℂ) ^ 2 / thetaDerivativeScalar *
      shapeOrderPhase s (c0 * ∏ i, p i) ^ n
  have hprod : c0 * ∏ i, p i ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hscalar (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      normalizedScalar n (D.datum hN hr hbase s hp hc0 v) =
        C * star (complexCharacter (D.relativeGamma hN hr hbase v)) := by
    have he := fixedCusp_normalizedScalar n s (D.sourceGamma hN hr hbase v)
      (c0 * ∏ i, p i) hprod (by rw [D.sourceGamma_mul, D.denominator])
    simpa only [C, ControlledStratumArithmetic.datum, D.sourceGamma_character] using he
  calc
    _ = C * (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
        fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
          star (complexCharacter (D.relativeGamma hN hr hbase v)) *
          ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) *
            (eisEmbedding x / eisLam ^ 4)) /
              (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hscalar]
      ring
    _ = _ := by
      rw [controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S x]
      dsimp only [C]
      ring

#print axioms controlled_normalized_multiplier

end OAI.CubicEisenstein.AngularControlledScalar
