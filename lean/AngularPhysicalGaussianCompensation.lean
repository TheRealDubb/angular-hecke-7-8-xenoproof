import OAI.NumberTheory.DirichletL.Detector.GaussianCompensation
import AngularPhysicalGaussianPhysicalTuple

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def compensationSubsetCoefficient {K : ℕ} (η : AngularCharacter)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (η.elementCoeff (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K : ℕ} (η : AngularCharacter) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    PhysicalDetectorProbe.markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

lemma compensatedTuple_eq_subsets {K : ℕ} (η : AngularCharacter) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    PhysicalDetectorProbe.compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : AngularCharacter) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    PhysicalDetectorProbe.compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold PhysicalDetectorProbe.compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

theorem compensationSubsetProbe_eq_gaussian_rows {K : ℕ} (η : AngularCharacter) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensationSubsetProbe η C W0 W1 p J X Y Z=
      compensationSubsetCoefficient η p J*
        ∑'r : PhysicalRowIndex,
          physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
            correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
              (physicalRowMonoid η C r) gaussianCompletedProfile
                (Z*elementNorm (slotProduct p (Finset.univ\J))) := by
  unfold compensationSubsetProbe
  rw [markedPhysicalProbe_eq_gaussian_rows η C _ W0 W1 hW0 hW1 _ _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J))
    (mul_pos hZ (slotProduct_norm_pos p hp _))]

end SevenEighths.Angular.PhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.compensatedTuple_eq_subsets

#print axioms OAI.SevenEighths.Angular.PhysicalLow.compensatedPhysicalProbe_eq_subsets

#print axioms OAI.SevenEighths.Angular.PhysicalLow.compensationSubsetProbe_eq_gaussian_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.compensationSubsetProbe_eq_gaussian_rows
