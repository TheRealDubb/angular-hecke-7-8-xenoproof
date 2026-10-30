import AngularPhysicalDetectorHighSelectedEstimate
import AngularPhysicalDetectorHighSelectedHolomorphy

/- Actual angular adaptation of pinned OAI-003 source proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow ProbePrimePower ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (unitPart unitPart_coprime multiplicity_lt_six
  selectedFirstBound compensatedReplacement_crude)
local notation "O" => ActualEisensteinCubic.O

lemma elementCoeff_zero_or_norm_one (eta : AngularCharacter) (p : O) :
    eta.elementCoeff p=0 ∨ ‖eta.elementCoeff p‖=1 := by
  by_cases h : eta.elementCoeff p=0
  · exact Or.inl h
  · right
    have hunit := not_or.mp (mt (eta.elementCoeff_zero_iff p).mpr h)
    let : Finite (O ⧸ eta.modulus) := Ring.HasFiniteQuotients.finiteQuotient eta.modulus_ne_bot
    let : Fintype (O ⧸ eta.modulus) := Fintype.ofFinite _
    obtain ⟨u,hu⟩ := not_not.mp hunit.2
    rw [eta.norm_elementCoeff hunit.1,←hu]
    exact FiniteRayExpansion.norm_char_unit eta.residue u

def actualUnramifiedSelected (eta : AngularCharacter) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedSelected (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (eta.elementCoeff p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

theorem actualUnramifiedSelected_bound (eta : AngularCharacter) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : theta≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,targetMonoid,AngularCharacter.elementHom,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

lemma continuedCompensatedLocal_ramified_bound (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : theta≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        385*(P.val.absNorm:ℝ)^(max (1-w.re) 0) := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
  have hb := ramifiedSelected_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  simpa only [hspan] using hb

lemma continuedCompensatedLocal_unramified_bound (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : ¬P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : theta≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤961 := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hP
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    exact (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η p) x z‖<1 := by
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact (rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num)
  rw [continuedCompensatedLocal_unramified η u P hs hP x w z hV hR]
  have hb := actualUnramifiedSelected_bound η p u.val hg.1 hg.2 hu (hspan.symm ▸ hQ) x w z hx hw hz
  have he : η.idealHom P.val=η.elementCoeff p := by rw [←hspan,η.idealHom_span]
  have hv : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  simpa only [actualUnramifiedSelected,hspan,he,hv] using hb

lemma continuedCompensatedLocal_bound (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : theta≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        961*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(max (1-w.re) 0) else 1) := by
  have hx0 : (874:ℝ)/1000 ≤ x.re := theta_bounds.1.le.trans hx
  by_cases hp : P.val∣Ideal.span {u.val}
  · rw [ite_eq_left hp]
    apply (continuedCompensatedLocal_ramified_bound η u P hs hp hQ x w z hx hw hz).trans
    gcongr
    norm_num
  · simpa only [ite_eq_right hp,mul_one] using continuedCompensatedLocal_unramified_bound η u P hs hp hQ x w z hx hw hz

theorem continuedCompensatedLocal_first_bound (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (R : ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hxR : x.re≤R) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        selectedFirstBound P.val.absNorm R := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  have hV := first_region_V_half _ hQ z hz
  have hD : ‖coordD P.val.absNorm (η.idealHom P.val) (idealRowHom u.val P.val) x‖≤1/2 :=
    (coordD_norm_le _ hQ0 _ _ x (AngularCharacter.norm_idealHom_le_one η _) (idealRowHom_norm u.val _)).trans
      (rpow_le_half _ _ hQ (by linarith))
  have hM : ‖continuedMarkedLocal η u P hs x w z‖≤388 := by
    rw [continuedMarkedLocal_eq_quotient η u P hs x w z
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV),div_eq_mul_inv,norm_mul]
    have hH := ramifiedCorrection_first_bound η u P hs hQ x w z hx hw hz hxw
    have hn : ‖ramifiedCorrection η u P hs x w z-1‖≤194 := by
      have h := norm_sub_le (ramifiedCorrection η u P hs x w z) (1:ℂ)
      rw [norm_one] at h
      linarith
    exact (mul_le_mul hn (ProbeLocal.inv_one_sub_norm_le_two _ hV) (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hW : ‖coordW P.val.absNorm (idealRowHom u.val P.val) w‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) :=
    (coordW_norm_le _ hQ0 _ w (idealRowHom_norm u.val _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hq : ‖(P.val.absNorm:ℂ)^(-w)‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) := by
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hB : ‖star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x‖≤(P.val.absNorm:ℝ)^R := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (AngularCharacter.norm_idealHom_le_one η _)).trans
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hxR
  exact compensatedReplacement_crude _ _ _ _ _ _ _ _ (by positivity) (by positivity)
    (hV.trans (by norm_num)) hW hD hM hB hq


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.elementCoeff_zero_or_norm_one

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actualUnramifiedSelected_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_ramified_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_unramified_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_bound

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_first_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCompensatedLocal_first_bound
