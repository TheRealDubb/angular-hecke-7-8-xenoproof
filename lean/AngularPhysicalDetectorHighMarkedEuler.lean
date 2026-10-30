import AngularPhysicalDetectorHighSignal
import OAI.NumberTheory.DirichletL.PrimeRows.MarkedNormalization

/- Actual angular adaptation of pinned OAI-003 proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeEulerFinsupp
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (rowCharacter rowCharacter_hasProd markExclusions markExclusions_prime
  mem_markExclusions lift_outside_hasProd)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

lemma markedIdealHighSummand_mark (S : Finset Id) (D : Id) (η : AngularCharacter)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

def excludedRowArray (S : Finset Id) (η : AngularCharacter) (u : O) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedRowArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : O) (x w z : ℂ) : excludedRowArray S η u x w z 1=1 := by
  simp only [excludedRowArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]

lemma excludedRowArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : O) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedRowArray S η u x w z (a*b)=excludedRowArray S η u x w z a*excludedRowArray S η u x w z b := by
  simp only [excludedRowArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedRowPrimeTerm (S : Finset Id) (η : AngularCharacter) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedRowArray S η u x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedRowArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : O) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedRowArray S η u x w z (highIdeals v)=v.prod (excludedRowPrimeTerm S η u x w z) :=
  highArray_val_prod _ (excludedRowArray_one S hS η u x w z) (excludedRowArray_mul S hS η u x w z) v

lemma markedRowArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : AngularCharacter) (u : O) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η u x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedRowArray S η u x w z (highIdeals v)=_
  rw [excludedRowArray_prod S hS]

theorem markedRowSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η u x w z) := by
  have h0 (P : PrimeIdeal) : excludedRowPrimeTerm S η u x w z P 0=1 := by
    simp only [excludedRowPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedRowArray_one S hS η u x w z
  have hs := (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedRowArray S η u x w z (highIdeals v)‖) at hs
  simp only [excludedRowArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedRowPrimeTerm S η u x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedRowPrimeTerm S η u x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η u x w z := by
    simp only [←markedRowArray_val S hS T η u x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (ProbePhysical.NonzeroIdeal×ProbePhysical.NonzeroIdeal)×(ProbePhysical.NonzeroIdeal×ProbePhysical.NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

def idealRowMarkedLocalFactor (η : AngularCharacter) (u : O) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*rowHighPrimeTerm η u x w z P ((e.val,l),(k,m))

lemma markedRowPrimeTerm_summable_norm (η : AngularCharacter) (u : O) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*rowHighPrimeTerm η u x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedRowPrimeTerm_tsum (η : AngularCharacter) (u : O) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,completedValuationMark P b*rowHighPrimeTerm η u x w z P b)=
      idealRowMarkedLocalFactor η u P x w z := by
  have hs := (markedRowPrimeTerm_summable_norm η u P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*rowHighPrimeTerm η u x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedRowLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : AngularCharacter) (u : O) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedRowPrimeTerm S η u x w z) P b)=
      if P∈T then idealRowMarkedLocalFactor η u P x w z else idealRowHighLocalFactor η u P.val x w z := by
  have he (b : HighValuation) : excludedRowPrimeTerm S η u x w z P b=rowHighPrimeTerm η u x w z P b := by
    simp only [excludedRowPrimeTerm,excludedRowArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,rowHighPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [ite_eq_left hPT]
    exact markedRowPrimeTerm_tsum η u P x w z hx hw hz
  · simp only [ite_eq_right hPT,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

theorem markedRowSeries_eq_finite_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then idealRowMarkedLocalFactor η u P x w z else 1
  have hR : HasProd R (∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hP : P∈T
    · rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP)),
        selectedRowLocal_outside S hS T η u P (hT P hP) x w z hx hw hz,ite_eq_left hP]
      simp only [R,ite_eq_left hP,one_mul]
    · simp only [R,ite_eq_right hP,mul_one,markedLocal,one_mul]
      change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
      rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedRowSeries_hasProd S hS T η u x w z hx hw hz).unique he'

theorem markedRowSeries_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let S' := markExclusions S T
    let hS' := markExclusions_prime S hS T
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S' hS') (6*z)*HeckeFamily.LFunction (rowCharacter S' hS' u) w/
        FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S' hS') x*globalCorrection S' η u x w z)*
        ∏P∈T,idealRowMarkedLocalFactor η u.val P x w z := by
  dsimp only
  rw [markedRowSeries_eq_finite_replacement S hS T hT η u.val x w z hx hw hz,
    high_L_factorization (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz]


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.markedRowSeries_hasProd

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.markedRowSeries_eq_finite_replacement

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.markedRowSeries_L_factorization
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.markedRowSeries_L_factorization
