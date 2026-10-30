import OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
import AngularPhysicalLowSlotPolynomial

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

def lowSingleSlotWeight (η : AngularCharacter) (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (η.elementCoeff a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

lemma lowSelectedWeight_eq_product {K : ℕ} (η : AngularCharacter) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : η.elementCoeff (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,η.elementCoeff (b i).val := map_prod (PhysicalDetectorProbe.targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm (η : AngularCharacter) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (PhysicalDetectorProbe.targetMonoid_norm_le_one η a)

lemma lowSingleSlotWeight_height_norm (η : AngularCharacter) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖=‖lowSingleSlotWeight η W P 0 a‖ := by
  simp only [lowSingleSlotWeight,norm_mul,logPhase_norm,mul_one]

lemma lowSelectedWeight_norm {K : ℕ} (η : AngularCharacter) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤∏i : SelectedSlot J,‖W i.val (elementNorm (b i).val/P i.val)‖ := by
  rw [lowSelectedWeight_eq_product,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>lowSingleSlotWeight_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_height_norm {K : ℕ} (η : AngularCharacter) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖=‖lowSelectedWeight η slots J W P 0 b‖ := by
  rw [lowSelectedWeight_eq_product,lowSelectedWeight_eq_product,norm_prod,norm_prod]
  exact Finset.prod_congr rfl (fun i _=>lowSingleSlotWeight_height_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_norm_le_one {K : ℕ} (η : AngularCharacter) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (hW : ∀i x,‖W i x‖≤1) (t : ℝ) (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤1 :=
  (lowSelectedWeight_norm η slots J W P t b).trans
    (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i.val _))

end SevenEighths.Angular.PhysicalLow
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedWeight_eq_product

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSingleSlotWeight_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSingleSlotWeight_height_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedWeight_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedWeight_height_norm

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSelectedWeight_norm_le_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.lowSelectedWeight_norm_le_one
