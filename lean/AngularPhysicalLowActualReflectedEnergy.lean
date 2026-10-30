import OAI.NumberTheory.DirichletL.Detector.LowActualReflectedEnergy
import AngularPhysicalLowActualIdealLists

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem lowSelectedInverseRow_actual_ideal {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (z : O) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        lowActualIdealPolynomial
          (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
          (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
          (rowTwist (physicalRayAngularBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X := by
  rw [lowSelectedInverseRow_correction]
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp_rw [lowSelectedWeight_eq_product]
  have hm (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0) := by
    funext A
    exact lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b) A
  simp_rw [hm,←physical_markedCompletedT_absorb_true_period η S hS hbad σ χ]
  convert low_actual_ideal_polynomial η S hS hbad (fun i : SelectedSlot J=>T i.val)
    (fun i=>hT i.val) (fun i=>hout i.val) (fun i=>W i.val) (fun i=>Y i.val) t
    (fun p=>InverseMoment.markedCompletedT
      (rowTwist (physicalRayAngularBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
      (fun A=>∏i : SelectedSlot J,if p i∣A then (1:ℂ) else 0)) using 1
  · congr 1
    ext p
    simp
  · rfl

theorem lowSelectedInverseRow_actual_reflected_energy {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
    lowCorrectionEnergy*∑χ : RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
      ‖lowActualIdealPolynomial
        (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayAngularBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) X‖^2 := by
  simp_rw [lowSelectedInverseRow_actual_ideal η S hS hbad T hT hout hdis J W Y X t σ]
  apply (fixed_correction_energy R ProbeCompleted.correctionCoeff _).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayAngularBase η S hS σ χ)
    (lowReflectionMask η S hS) (fun Ψ=>lowActualIdealPolynomial
      (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
      (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I)) Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X)

end SevenEighths.Angular.PhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedInverseRow_actual_ideal

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedInverseRow_actual_reflected_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.lowSelectedInverseRow_actual_reflected_energy
