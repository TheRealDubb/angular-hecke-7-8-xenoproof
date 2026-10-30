import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial
import AngularPhysicalLowSelectedSum

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

def lowSelectedWeight {K : ℕ} (η : AngularCharacter) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) : ℂ :=
  star (η.elementCoeff (∏i : SelectedSlot J,(b i).val))*
    ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
      FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val))

lemma lowSlotJoin_weight {K : ℕ} (η : AngularCharacter) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    compensationSubsetWeight η W P (lowSlotJoin slots J a b) J*
      selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
        lowUnselectedWeight slots J W P a*lowSelectedWeight η slots J W P t b := by
  unfold compensationSubsetWeight compensationSubsetCoefficient
  rw [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct]
  simp only [selectedSlotFactor,lowSlotJoin_selected]
  rw [←Finset.prod_coe_sort J (fun i=>W i (elementNorm (lowSlotJoin slots J a b i)/P i))]
  simp only [lowSlotJoin_unselected]
  unfold lowUnselectedWeight lowSelectedWeight
  ring

lemma compensationRowTest_join_low {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 (lowSlotJoin slots J a b) J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
  simpa only [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSelectedIdeal] using
    compensationRowTest_low_separated η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
      (lowSlotJoin slots J a b) (lowSlotJoin_nonzero slots hslots J a b) J X Y T t hX hY hT

theorem compensation_tuple_low_polynomial {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    (∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  rw [sum_lowSlotJoin slots J (fun p=>compensationSubsetWeight η W P p J*
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t*selectedSlotFactor W P p J t)]
  apply Finset.sum_congr rfl
  intro a ha
  let L := elementNorm (∏i : J,(a i).val)
  have hL : 0<L := lowUnselectedProduct_norm_pos slots hslots J a
  let C := calibrationForSet S hS
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  let N : ℂ := (Real.sqrt (lowPhysicalScale C (X/L) (Y/L)):ℂ)⁻¹*(1/(2*Real.pi):ℂ)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩc : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  calc
    _ = lowUnselectedWeight slots J W P a*N*
        ∑b : LowSelectedTuple slots J,lowSelectedWeight η slots J W P t b*
          ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω (X/L) (Y/L)
            (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [compensationRowTest_join_low η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
        slots hslots J a b X Y T t hX hY hT]
      have hw := lowSlotJoin_weight η slots J W P t a b
      dsimp only [C,Ω,L,N]
      linear_combination (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*
        (1/(2*Real.pi):ℂ)*(∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v)*hw
    _ = _ := by
      rw [lowSeparatedIntegral_finite_sum Finset.univ (lowSelectedWeight η slots J W P t)
        C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩc hΩ0 (X/L) (Y/L)
        (div_pos hX hL) (div_pos hY hL)]
      rfl

end SevenEighths.Angular.PhysicalLow
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowSlotJoin_weight


#print axioms OAI.SevenEighths.Angular.PhysicalLow.compensationRowTest_join_low

#print axioms OAI.SevenEighths.Angular.PhysicalLow.compensation_tuple_low_polynomial
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.compensation_tuple_low_polynomial
