import AngularPhysicalDetectorCentralSplit
import OAI.NumberTheory.DirichletL.Detector.RaySlots
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralLower
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Topology
open Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily ProbePhysical ProbeRaySlots
local notation "O" => HeckeFamily.O
theorem prime_coprime_of_norm_gt (η : AngularCharacter) (P : ProbePhysical.PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

theorem central_pool_good_eventually (η : AngularCharacter) (e c b dmin rmin : ℝ)
    (he : 0<e) (hc : 0<c) (hcb : c≤b) (hd : 0<dmin) (hr : 0<rmin) :
    ∀ᶠ Z : ℝ in atTop,∀(C : Set (Ideal O)) (S : Finset (Ideal O)) (d r : ℝ),dmin≤d → rmin≤r →
      ∀P∈pool C S c b ((Z^d)^r),P.val∉S ∧ IsCoprime P.val η.modulus ∧
        (480:ℝ)≤P.val.absNorm ∧ 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2 := by
  obtain ⟨Q0,hQ0,hsmall⟩ := ProbeEuler.central_correction_threshold e he
  have ht := (tendsto_rpow_atTop (mul_pos hd hr)).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop Q0),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ))] with Z hZ hQ hη
  intro C S d r hdd hrr P hP
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hle : c*Z^(dmin*rmin)≤c*(Z^d)^r := by
    rw [←Real.rpow_mul hZp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul hdd hrr hr.le (hd.trans_le hdd).le)) hc.le
  have hl := (pool_norm_bounds C S hc.le hcb hD P hP).1
  have hq : Q0≤(P.val.absNorm:ℝ) := hQ.trans (hle.trans (by linarith))
  exact ⟨(mem_pool C S c b _ P).mp hP |>.2.2.2,
    prime_coprime_of_norm_gt η P (hη.trans_le (hle.trans (by linarith))),hQ0.trans hq,hsmall _ hq⟩


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.prime_coprime_of_norm_gt

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.central_pool_good_eventually
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.central_pool_good_eventually
