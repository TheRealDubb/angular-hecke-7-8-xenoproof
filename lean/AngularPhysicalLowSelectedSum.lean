import OAI.NumberTheory.DirichletL.Detector.LowSelectedSum
import AngularPhysicalLowCompensation

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSelectedInverseRow {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : AngularCharacter) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*lowMarkedInverseRow η S hS (D k) T t σ m

lemma lowSelectedInverseRow_correction {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : AngularCharacter) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) :
    lowSelectedInverseRow F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayAngularBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0) := by
  unfold lowSelectedInverseRow lowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SevenEighths.Angular.PhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedInverseRow_correction
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.lowSelectedInverseRow_correction
