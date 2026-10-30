import AngularPhysicalDetectorActualTupleRows
import AngularPhysicalDetectorActualAbsoluteRows

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CubicEisenstein ProbePhysical ProbeMellinBoundary
open HeckeFamily HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

open CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
open scoped ContDiff


lemma tupleSourceTripleIntegral_eq_rows {K : ℕ} (η : AngularCharacter) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O)
    (hp : ∀i,p i≠0) (X Y Z : ℝ) :
    tupleSourceTripleIntegral η S C W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S C W0 W1 p X Y Z := by
  unfold tupleSourceTripleIntegral compensatedRowTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact tupleSourceSeries_eq_rows η S C p hp
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem compensatedTuple_eq_row_triple {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    PhysicalDetectorProbe.compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  rw [compensatedTuple_eq_source_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    p hp X Y Z hX hY hZ,tupleSourceTripleIntegral_eq_rows η S _ W0 W1 p hp]

theorem compensatedPhysicalProbe_eq_row_triples {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (slotPrimes : Fin K→Finset O) (hp : ∀i a,a∈slotPrimes i→a≠0)
    (slotWindow : Fin K→ℝ→ℂ) (slotScale : Fin K→ℝ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    PhysicalDetectorProbe.compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1 slotPrimes slotWindow slotScale X Y Z=
      ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
        (∏i,slotWindow i (elementNorm (p i).val/slotScale i))*
        compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) X Y Z := by
  unfold PhysicalDetectorProbe.compensatedPhysicalProbe
  apply Finset.sum_congr rfl
  intro p _
  rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (fun i=>(p i).val) (fun i=>hp i (p i).val (p i).property) X Y Z hX hY hZ]


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.tupleSourceTripleIntegral_eq_rows

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.compensatedTuple_eq_row_triple

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.compensatedPhysicalProbe_eq_row_triples
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.compensatedPhysicalProbe_eq_row_triples
