import AngularPhysicalOriginalSourceIdentity
import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.InputParentCapacity
open PlainRows.CommonRows
open CenteredMomentEnergyBands (length)
open CenteredMomentEnergyInputParentCapacity (raw_log_le_length)
variable {ι:Type*} [Fintype ι]
theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

theorem input_reference_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (s.Y₁*s.Y₂*∏i,s.P i)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [s.same_product]
  exact input_affine_capacity s Z κ M hZ hcap

theorem original_slot_logs (s:Input ι)(Z:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hw:∀i,0≤w i)(hP:∀i,s.P i=Z^(w i)):
    (∀i,1≤s.P i) ∧ (∀i,Real.logb Z (s.P i)=w i) := by
  constructor
  · intro i;rw [hP i];exact Real.one_le_rpow hZ.le (hw i)
  · intro i;rw [hP i,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem original_exponent_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hP:∀i,s.P i=Z^(w i))
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,w i)≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  apply input_affine_capacity s Z κ M hZ
  simpa only [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap

theorem original_volume_cap (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(hk:1/6≤κ)
    (hP:∀i,1≤s.P i)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    volume s≤Z^M := by
  have hh:=input_affine_capacity s Z κ M hZ hcap
  have hn:0≤∑i,Real.logb Z (s.P i):=
    Finset.sum_nonneg (fun i _=>Real.logb_nonneg hZ (hP i))
  have hp:0≤(6*κ-1)*(∑i,Real.logb Z (s.P i)):=mul_nonneg (by linarith) hn
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (by linarith)

end OAI.SevenEighths.Angular.InputParentCapacity

#print axioms OAI.SevenEighths.Angular.InputParentCapacity.input_volume_log
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.InputParentCapacity.input_volume_log

#print axioms OAI.SevenEighths.Angular.InputParentCapacity.input_affine_capacity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.InputParentCapacity.input_affine_capacity

#print axioms OAI.SevenEighths.Angular.InputParentCapacity.input_reference_affine_capacity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.InputParentCapacity.input_reference_affine_capacity

#print axioms OAI.SevenEighths.Angular.InputParentCapacity.original_slot_logs
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.InputParentCapacity.original_slot_logs

#print axioms OAI.SevenEighths.Angular.InputParentCapacity.original_exponent_capacity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.InputParentCapacity.original_exponent_capacity

#print axioms OAI.SevenEighths.Angular.InputParentCapacity.original_volume_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.InputParentCapacity.original_volume_cap
