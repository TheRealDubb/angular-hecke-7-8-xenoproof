import OAI.NumberTheory.DirichletL.Detector.LowPrimeFamily
import AngularPhysicalLowSlotWeights

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem lowCanonicalInverseRow_eq {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J)
    (R t : ℝ) (σ : RayRing) (m : O) :
    lowMarkedInverseRow η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b) R t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayAngularBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) R
          (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
  unfold lowMarkedInverseRow
  have he : (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      (fun A : Id=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  rw [he]

end SevenEighths.Angular.PhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowCanonicalInverseRow_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.lowCanonicalInverseRow_eq
