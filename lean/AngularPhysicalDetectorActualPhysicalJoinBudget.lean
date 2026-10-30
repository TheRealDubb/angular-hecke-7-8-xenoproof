import AngularPhysicalDetectorActualBandParameters

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

/-- The already constructed retained parameters also pay the physical
source-tail error after division by the actual principal normalizer. -/
lemma actual_physical_join_budget (p : ActualRetainedParameters) :
    0 < p.e ∧ p.e < 1/1000 ∧ 0 < p.ζ ∧ p.ζ ≤ 1/48 ∧ p.eps ≤ 1 ∧
    8*p.e+p.normalizerLoss+p.saving ≤ 63/800 ∧
    p.normalizerLoss+p.saving ≤ 1 := by
  rcases p.early_conditions with ⟨hew,hew1,hewM,hewr,he,he1,her,hrest⟩
  rcases p.mesh_conditions with ⟨hem,hem1,hR,hmesh,hnu,hcc,hcommon⟩
  rcases p.loss_conditions with ⟨hz,hm,hpad,hn,hd,hs,hl,hphase⟩
  rcases p.geometry_conditions with ⟨hzm,hztop,hpm⟩
  rcases p.epsilon_conditions with ⟨heps,hepsr⟩
  have hN : (0:ℝ) ≤ p.N := Nat.cast_nonneg _
  have hNeps : 0 ≤ (p.N+8)*p.eps := by positivity
  have hcount : 0 ≤ 159*p.epsw+p.epsm+p.R+7*p.nu+p.countCost := by positivity
  have hsmall := p.rho_small
  have hbudget := p.central_budget
  refine ⟨he,he1,hz,by linarith,?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- A pointwise join, with the exact same central cube in both hypotheses.
It does not choose new windows and does not evaluate the principal pool. -/
lemma actual_normalized_physical_join
    (p : ActualRetainedParameters) (beta Z Q Ccentral Cerror Cnormalizer : ℝ)
    (hbeta : (7/8:ℝ) ≤ beta) (hZ : 1 ≤ Z) (hQ : 1 ≤ Q)
    (hc0 : 0 ≤ Ccentral) (he0 : 0 ≤ Cerror) (hn0 : 0 ≤ Cnormalizer)
    (probe principal cube normalizer : ℂ)
    (hcentral : ‖cube/normalizer‖ ≤ Ccentral*Q^(2*p.eps)*Z^(3/16-p.saving))
    (herror : ‖probe-principal-cube‖ ≤
      Cerror*Q^2*(Z^(beta-11/16-63/800+8*p.e)+Z^(-1:ℝ)))
    (hnormalizer : ‖normalizer⁻¹‖ ≤ Cnormalizer*Z^p.normalizerLoss) :
    ‖(probe-principal)/normalizer‖ ≤
      (Ccentral+2*Cerror*Cnormalizer)*Q^2*Z^(beta-11/16-p.saving) := by
  rcases actual_physical_join_budget p with ⟨_,_,_,_,heps,hbudget,hbudget1⟩
  have hZp : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQpow : Q^(2*p.eps) ≤ Q^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have hZcentral : Z^(3/16-p.saving) ≤ Z^(beta-11/16-p.saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hZtail : Z^(beta-11/16-63/800+8*p.e+p.normalizerLoss) ≤
      Z^(beta-11/16-p.saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hZcube : Z^((-1:ℝ)+p.normalizerLoss) ≤ Z^(beta-11/16-p.saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hc : ‖cube/normalizer‖ ≤ Ccentral*Q^2*Z^(beta-11/16-p.saving) := by
    apply hcentral.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQpow hc0) hZcentral
      (Real.rpow_nonneg hZp.le _) (mul_nonneg hc0 (sq_nonneg Q))
  have he : ‖(probe-principal-cube)/normalizer‖ ≤
      (2*Cerror*Cnormalizer)*Q^2*Z^(beta-11/16-p.saving) := by
    calc
      _ = ‖probe-principal-cube‖*‖normalizer⁻¹‖ := by rw [div_eq_mul_inv,norm_mul]
      _ ≤ (Cerror*Q^2*(Z^(beta-11/16-63/800+8*p.e)+Z^(-1:ℝ)))*
          (Cnormalizer*Z^p.normalizerLoss) :=
        mul_le_mul herror hnormalizer (norm_nonneg _) (by positivity)
      _ = Cerror*Cnormalizer*Q^2*
          (Z^(beta-11/16-63/800+8*p.e+p.normalizerLoss)+Z^((-1:ℝ)+p.normalizerLoss)) := by
        rw [Real.rpow_add hZp (beta-11/16-63/800+8*p.e) p.normalizerLoss,
          Real.rpow_add hZp (-1) p.normalizerLoss]
        ring
      _ ≤ Cerror*Cnormalizer*Q^2*
          (Z^(beta-11/16-p.saving)+Z^(beta-11/16-p.saving)) :=
        mul_le_mul_of_nonneg_left (add_le_add hZtail hZcube) (by positivity)
      _ = _ := by ring
  calc
    _ = ‖(probe-principal-cube)/normalizer+cube/normalizer‖ := by congr 1;ring
    _ ≤ ‖(probe-principal-cube)/normalizer‖+‖cube/normalizer‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add he hc).trans_eq (by ring)

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_physical_join_budget
#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_normalized_physical_join
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_normalized_physical_join
