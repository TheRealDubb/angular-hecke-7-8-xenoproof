import AngularHybridEnergy
import OAI.NumberTheory.DirichletL.Reflection.WeightedSourceSum

/-! The separated angular weights are the literal geometric and dual phases
of the actual physical reflected row. Common fixed factors and cusp columns
are explicit finite-sector hypotheses, as in the pinned original identity. -/
namespace OAI.CubicEisenstein.AngularPhysicalHybrid
open scoped Classical BigOperators
open SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
open InverseReflectedPhase Angular AngularPhaseSeparation AngularControlledScalar AngularHybridEnergy
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

theorem reflected_shape_phase (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis)
    (hK : Admissible K) (S : PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) :
    shapeOrderPhase s (c * ∏ i, (F.reflected K hK S).generator i) ^ order =
      shapeOrderPhase s (c * ∏ i, F.generator i) ^ order *
        denominatorPhase (primaryGenerator K) ^ order *
        denominatorPhase (primaryGenerator (∏ i, S.ideal i)) ^ order := by
  rw [(F.reflected K hK S).generator_product, F.reflected_product,
    primaryGenerator_mul, primaryGenerator_mul, F.generator_product]
  exact physical_row_slot_phase _ _ _ _ _ _

def angularWeightedPhysicalReflectedRow (order : ℕ) (F : PrimeFamily φ)
    (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis → PrimeFamily σ)
    (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    r K * aw P.val * w n b * (if h : IsCoprime K P.val then
      actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b *
        alpha (fixedCuspArrayIndex u m n b) ^ order *
        shapeOrderPhase s (c * ∏ i, (F.reflected K hK (S P.val)).generator i) ^ order else 0)

theorem angularWeightedPhysicalReflectedRow_separate (order : ℕ) (F : PrimeFamily φ)
    (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis → PrimeFamily σ)
    (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i) = P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) :
    angularWeightedPhysicalReflectedRow order F K hK S jF Pset nset bset D s hc r aw w u m =
      shapeOrderPhase s (c * ∏ i, F.generator i) ^ order *
        weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
          (angularIdealWeight order r) (angularIdealWeight order aw) (angularDualWeight order u m w) u m := by
  unfold angularWeightedPhysicalReflectedRow weightedPhysicalReflectedRow
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : IsCoprime K P.val
  · rw [dif_pos h, dif_pos h, reflected_shape_phase, hprod P.val P.property]
    unfold angularIdealWeight angularDualWeight
    ring
  · simp only [dif_neg h, mul_zero]

theorem angularWeightedPhysicalReflectedRow_eq_branches (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) :
    angularWeightedPhysicalReflectedRow order F K hK S jF Pset nset bset D s hc r aw w u m =
      shapeOrderPhase s (c * ∏ i, F.generator i) ^ order *
        ∑ e : φ → Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (angularIdealWeight order r)
          (angularIdealWeight order aw) (angularDualWeight order u m w) u m Pset nset bset K := by
  rw [angularWeightedPhysicalReflectedRow_separate order F K hK S jF Pset nset bset hprod D s hc r aw w u m]
  rw [weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop G0 D0 s hc hκ hA hb]

#print axioms angularWeightedPhysicalReflectedRow_eq_branches
end
end OAI.CubicEisenstein.AngularPhysicalHybrid
