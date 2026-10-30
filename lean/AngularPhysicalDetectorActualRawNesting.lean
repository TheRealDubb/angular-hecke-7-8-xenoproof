import AngularPhysicalDetectorActualRawPhysicalIntegral
import OAI.NumberTheory.DirichletL.Detector.RawNesting

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

local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩
def originalNestedOnLines (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (p : PhysicalNestedSpace S) : ℂ :=
  originalRawOnLines η S hS D W0 W1 X Y Z
    ⟨(p.2.2.2.2.2,(p.2.2.2.1,p.1.val)),p.1.property⟩ ((p.2.2.1,p.2.2.2.2.1),p.2.1)

theorem originalRaw_integral_eq_nesting (η : AngularCharacter)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
    ∑'K : SourceOuter S,∫w : ℝ,∫t : ℝ,∑'IJ : CompletedPair,∫z : ℝ,∑'H : NonzeroFrequency,
      originalNestedOnLines η S hS D W0 W1 X Y Z (K,(w,(t,(IJ,(z,H))))) := by
  have hi := originalRaw_counting_product_integrable η S hS hpS hbad D W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp := physicalRawNesting_preserving S
  have hj := (hp.symm (physicalRawNesting S)).integrable_comp_of_integrable hi
  have he := hp.integral_comp' (originalNestedOnLines η S hS D W0 W1 X Y Z)
  have he' : (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
      ∫p : PhysicalNestedSpace S,originalNestedOnLines η S hS D W0 W1 X Y Z p
        ∂((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
          ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
    exact he
  rw [he']
  apply integral_physical_nesting
  exact hj


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.originalRaw_integral_eq_nesting
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.originalRaw_integral_eq_nesting
