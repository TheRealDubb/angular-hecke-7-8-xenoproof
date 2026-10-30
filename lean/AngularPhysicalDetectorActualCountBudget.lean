import AngularPhysicalDetectorLiteralCommonBins
import OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeDetectorWitnessRows HeckeDetectorClassBudget
lemma eventually_all_rpow_ge {P : ℝ→Prop} (hP : ∀ᶠU in atTop,P U)
    (dmin : ℝ) (hdmin : 0<dmin) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → P (Z^d) := by
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.1 hP
  have hh := (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop A)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  intro d hd
  exact hA _ (hZ.trans (Real.rpow_le_rpow_of_exponent_le hZ1 hd))

lemma source_count_frequency_eventually (n : ℕ) (dmax τ h : ℝ)
    (hdmax : 0<dmax) (hτ : 0<τ) (hh : τ<h) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≤dmax → ∀i : ℕ,i≤n →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤Z^h := by
  have hC := HeckeDyadic.constant_absorbed_eventually
    (2*Real.pi+3*(n:ℝ)) (h-τ) (by linarith)
  filter_upwards [hC,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro d hd i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hexp : d*(τ/(2*dmax))≤τ := by
    have h1 := mul_le_mul_of_nonneg_right hd (show 0≤τ/(2*dmax) by positivity)
    have h2 : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rw [h2] at h1
    linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^τ := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  calc
    _ ≤ (2*Real.pi+3*(n:ℝ))*Z^τ := by push_cast; nlinarith [Real.pi_pos,Real.rpow_pos_of_pos hZp τ]
    _ ≤ Z^(h-τ)*Z^τ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^h := by rw [←Real.rpow_add hZp];congr 1;ring

lemma source_dyadic_cost_eventually (dmin dmax loss : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hl : 0<loss) :
    ∃K : ℝ,0≤K ∧ ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
      (dyadicLength (Z^d):ℝ)^2≤K*Z^loss := by
  obtain ⟨K,hK,hbound⟩ := dyadic_cost_eventually (loss/dmax) (by positivity)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hbound dmin hdmin,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd'
  apply (hb d hd).trans
  apply mul_le_mul_of_nonneg_left _ hK
  rw [←Real.rpow_mul (zero_lt_one.trans_le hZ).le]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hh := mul_le_mul_of_nonneg_right hd' (show 0≤loss/dmax by positivity)
  simpa only [mul_div_cancel₀ _ hdmax.ne'] using hh


/-- The entire actual label/dyadic/profile prefactor is paid. The common
degree J is not replaced by a linear height cost. C may depend on the target,
so only the eventual scale, not the exponent, depends on C. -/
theorem actual_count_prefactor_eventually {Label : Type*} [Fintype Label]
    (J : ℕ) (C dmin dmax logCost heightPower countCost : ℝ)
    (hC : 0≤C) (hdmin : 0<dmin) (hdmax : 0<dmax)
    (hlog : 0<logCost) (hh : 0≤heightPower) (hcost : 0≤countCost)
    (hbudget : logCost+heightPower*J≤dmin*countCost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
      ((Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2)*
        (C*(1+Z^heightPower)^J)≤(Z^d)^countCost := by
  obtain ⟨K,hK,hdyadic⟩ := source_dyadic_cost_eventually dmin dmax (logCost/2)
    hdmin hdmax (by positivity)
  have hc := HeckeDyadic.constant_absorbed_eventually
    ((Fintype.card Label:ℝ)*K*C*(2:ℝ)^J) (logCost/2) (by positivity)
  filter_upwards [hdyadic,hc,eventually_ge_atTop (1:ℝ)] with Z hd hc hZ
  intro d hdlo hdhi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^heightPower := Real.one_le_rpow hZ hh
  have hprofile : (1+Z^heightPower)^J≤(2:ℝ)^J*Z^(heightPower*J) := by
    calc
      _ ≤ (2*Z^heightPower)^J := by gcongr;linarith
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hZp.le]
  calc
    _ ≤ ((Fintype.card Label:ℝ)*(K*Z^(logCost/2)))*
        (C*((2:ℝ)^J*Z^(heightPower*J))) := by
      gcongr
      exact hd d hdlo hdhi
    _ = ((Fintype.card Label:ℝ)*K*C*(2:ℝ)^J)*
        Z^(logCost/2)*Z^(heightPower*J) := by ring
    _ ≤ Z^(logCost/2)*Z^(logCost/2)*Z^(heightPower*J) := by gcongr
    _ = Z^(logCost+heightPower*J) := by
      rw [←Real.rpow_add hZp,←Real.rpow_add hZp]
      congr 1;ring
    _ ≤ (Z^d)^countCost := by
      rw [←Real.rpow_mul hZp.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      exact hbudget.trans (mul_le_mul_of_nonneg_right hdlo hcost)

lemma count_cost_absorption (U prefactor R countCost cardinality : ℝ)
    (hU : 0<U) (hc : cardinality≤prefactor*U^R)
    (hp : prefactor≤U^countCost) :
    cardinality≤U^(R+countCost) := by
  calc
    _ ≤ U^countCost*U^R := hc.trans
      (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hU.le _))
    _ = _ := by rw [←Real.rpow_add hU];congr 1;ring

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.eventually_all_rpow_ge

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.source_count_frequency_eventually

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.source_dyadic_cost_eventually

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_count_prefactor_eventually

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.count_cost_absorption
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.count_cost_absorption
