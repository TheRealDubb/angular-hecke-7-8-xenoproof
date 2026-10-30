import AngularPhysicalCell
import OAI.NumberTheory.DirichletL.Reflection.FullDyadic

/-! Dyadic reindexing of the exact angular reflected series, justified by
its proved absolute summability and retaining the full outer scalar. -/
namespace OAI.CubicEisenstein.AngularFullDyadic
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CompletedGauss CompletedDyadic SevenEighths.InverseMoment
open SevenEighths.InverseReflectedPhase AngularFullRaw AngularControlledScalar AngularMixedReflection
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def angularLiteralDyadicBlock (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (u : Eisˣ) (i : ℕ×ℕ×ℕ) : ℂ :=
  ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
    angularLiteralRawSeries order G D s hc j S W X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)

theorem angularMixedReflected_eq_dyadic (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    angularMixedReflected order D s G.generator_ne_zero hc G.generator_good j S W X=
      (fixedRadialCoefficientScalar/thetaDerivativeScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        shapeOrderPhase s (c*∏ i,G.generator i)^order)*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, angularLiteralDyadicBlock order G D s hc j S W X u i := by
  have hs := (angularLiteralRawSeries_summable_norm order G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [angularMixedReflected_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)


#print axioms angularMixedReflected_eq_dyadic
end
end OAI.CubicEisenstein.AngularFullDyadic
