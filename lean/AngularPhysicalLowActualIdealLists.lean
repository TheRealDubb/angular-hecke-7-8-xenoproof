import OAI.NumberTheory.DirichletL.Detector.LowActualIdealLists
import AngularPhysicalLowTruePeriodPuncture

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
namespace SevenEighths.Angular.PhysicalLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowPrimeIdealList_coprime (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (I : Id) (hI : I∈lowPrimeIdealList (lowPeriodPrimeList η S hS T)) :
    IsCoprime I (lowPeriodIdeal η S hS) := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact lowPeriodPrimeList_coprime η S hS T P hP

theorem low_actual_ideal_polynomial {ι : Type*} [Fintype ι]
    (η : AngularCharacter) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*F (fun i=>Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val) := by
  let E := Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))
  rw [←Equiv.sum_comp E]
  simp only [E,Equiv.piCongrRight_apply,Pi.map_apply,canonicalSlotEquiv_val]
  have hspan (p : ∀i,T i) (i : ι) : Ideal.span {primaryGenerator (p i).val.val}=(p i).val.val :=
    span_primaryGenerator_of_supported _ (hT i _ (p i).property)
  simp_rw [hspan]
  rw [low_canonical_polynomial_period_filter η S hS hbad T hT hout W Y t (fun p=>F (fun i=>(p i).val))]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun i=>lowPrimeListEquiv (lowPeriodPrimeList η S hS (T i))))
    (fun p=>(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val))

lemma low_actual_ideal_weight_bound (η : AngularCharacter) (W : ℝ→ℂ)
    (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) :
    ‖lowSingleSlotWeight η W Y t (primaryGenerator I)‖≤1 :=
  (lowSingleSlotWeight_norm η W Y t _).trans (hW _)

end SevenEighths.Angular.PhysicalLow
end
end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalLow.lowPrimeIdealList_coprime

#print axioms OAI.SevenEighths.Angular.PhysicalLow.low_actual_ideal_polynomial

#print axioms OAI.SevenEighths.Angular.PhysicalLow.low_actual_ideal_weight_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalLow.low_actual_ideal_weight_bound
