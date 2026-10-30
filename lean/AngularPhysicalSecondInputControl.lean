import AngularPhysicalMainSeparated
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.SecondInputControl
open PlainRows PlainRows.CommonRows
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma slot_product_le (s:Input ι)(N:ℕ)(C:ℝ)(hC:1≤C)
    (hN:Fintype.card ι≤N)(hM:∀i,s.M i≤C): (∏i,s.M i)≤C^N := by
  calc
    _≤∏_i:ι,C:=Finset.prod_le_prod₀ (fun i _=>(s.M_ge_one i).trans' zero_le_one) (fun i _=>hM i)
    _=C^(Fintype.card ι):=by simp
    _≤C^N:=pow_le_pow_right₀ hC hN

omit [DecidableEq ι] in
lemma lower_product (s:Input ι)(N:ℕ)(a:ℝ)(ha:0<a)
    (hN:Fintype.card ι≤N)(hlo:∀i,a≤s.lo i):
    (min 1 a)^N≤∏i,s.lo i := by
  have hm:0≤min 1 a:=le_min zero_le_one ha.le
  calc
    _≤(min 1 a)^(Fintype.card ι):=pow_le_pow_of_le_one hm (min_le_left _ _) hN
    _=∏_i:ι,min 1 a:=by simp
    _≤∏i,s.lo i:=Finset.prod_le_prod₀ (fun _ _=>hm) (fun i _=>(min_le_right _ _).trans (hlo i))


end OAI.SevenEighths.Angular.SecondInputControl

#print axioms OAI.SevenEighths.Angular.SecondInputControl.slot_product_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondInputControl.slot_product_le

#print axioms OAI.SevenEighths.Angular.SecondInputControl.lower_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondInputControl.lower_product
