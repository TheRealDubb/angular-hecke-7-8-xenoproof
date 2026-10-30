import AngularPhysicalDetectorActualCompensatedTriple
import AngularPhysicalDetectorActualGlobalPhysicalDyad
import OAI.NumberTheory.DirichletL.Detector.CanonicalSlots

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.Angular.PhysicalDetectorHigh
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve HeckeInverseAmplification
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensatedPhysicalProbe_canonical_slots {K : ℕ} (η : AngularCharacter)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) :
    PhysicalDetectorProbe.compensatedPhysicalProbe η C W0 W1 (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        PhysicalDetectorProbe.compensatedTuple η C W0 W1 (fun i=>primaryGenerator (P i).val.val) X Y Z :=
  sum_canonical_weighted_tuples T hT W Yp (fun p=>PhysicalDetectorProbe.compensatedTuple η C W0 W1 p X Y Z)

theorem finitePhysicalRows_canonical_slots {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(canonicalSlotSupport (T i))),
        (∏i,W i (elementNorm (p i).val/Yp i))*
          ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_canonical_weighted_tuples T hT W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem compensatedPhysicalProbe_eq_canonical_rows {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    PhysicalDetectorProbe.compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑'u : FreeRow,∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hn (P : ∀i,↥(T i)) (i : Fin K) : primaryGenerator (P i).val.val≠0 :=
    supported_primaryGenerator_ne_zero _ (hT i _ (P i).property)
  have hs (P : ∀i,↥(T i)) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [compensatedPhysicalProbe_canonical_slots η _ W0 W1 T hT W Yp]
  calc
    _ = ∑P : (∀i,↥(T i)),∑'u : FreeRow,(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
      rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
          _ (hn P) X Y Z hX hY hZ,
          compensatedRowTripleIntegral_eq_tsum η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
        exact tsum_mul_left.symm
    _ = _ := (Summable.tsum_finsetSum (fun P _=>hs P)).symm

theorem finitePhysicalRows_original_primary_slots {K : ℕ} (S : Finset Id)
    (hmax : ∀P∈S,P.IsMaximal) (η : AngularCharacter) (R : Finset FreeRow)
    (A : Fin K→Finset O) (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    finitePhysicalRows S hmax η R
      (fun i=>idealSlotOfPrimary (A i) (hp i)) W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Yp i))*
        ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_original_primary_weighted_tuples A hp hs hn W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end SevenEighths.Angular.PhysicalDetectorHigh
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.compensatedPhysicalProbe_canonical_slots

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finitePhysicalRows_canonical_slots

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.compensatedPhysicalProbe_eq_canonical_rows

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finitePhysicalRows_original_primary_slots
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.finitePhysicalRows_original_primary_slots
