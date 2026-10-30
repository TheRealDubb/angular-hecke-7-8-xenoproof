import AngularPhysicalEnergyState
import OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect
import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionGeometry
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.NaturalUnbalanced
open EnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBranchGeometry
open CenteredMomentEnergyOriginalHighReflectionGeometry (deleted_length_le)
local notation "O" => ActualEisensteinCubic.O
lemma divisor_norm {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1<Z)(hY:0<Y)(hN:0<N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (hZ:1<Z)(L Y:ℝ)(hwidth:s.width≤L)(hY:1≤Y)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

lemma original_long_positive (Z M X₁ X₂ ell κ:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:(3/4:ℝ)≤κ)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤M):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hbudget:=CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets M (length Z X₁+length Z X₂) ell κ 0 hell (by linarith)
    (by simpa only [sub_zero] using hlarge) (by linarith)
  have hpos:0<length Z X₂:=by linarith [hbudget.1]
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

theorem actual_deleted_gates {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (hZ:1<Z)(hM:0<s.width)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:(3/4:ℝ)≤κ)(hxi:0≤xi)(hxiM:xi≤s.width/16)
    (hshort:length Z X₁≤s.width/4)
    (hlarge:5*s.width/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ));
    let along:=Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ));
    Z^short=X₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):=by
  dsimp only
  have hZ0:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hp₁:=div_pos hX₁ (zero_lt_one.trans_le hn₁)
  have hp₂:=div_pos hX₂ (zero_lt_one.trans_le hn₂)
  have he₁:=Real.rpow_logb hZ0 hZ.ne' hp₁
  have he₂:=Real.rpow_logb hZ0 hZ.ne' hp₂
  have hd₁:=deleted_length_le Z X₁ _ hZ hX₁ hn₁
  have hd₂:=deleted_length_le Z X₂ _ hZ hX₂ hn₂
  have hraw₁:Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ))≤
      length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₁];exact le_max_right _ _
  have hraw₂:Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))≤
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₂];exact le_max_right _ _
  have hlen₁:=length_nonneg Z X₁ hZ
  have hlen₂:=length_nonneg Z X₂ hZ
  have hslot:0≤6*κ*ell:=mul_nonneg (by linarith) hell
  have hl:=original_long_positive Z s.width X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hshort hlarge hcap
  have hrange:=divisor_reflection_range s hZ Mcap X₂ hwidth hl.2.2 D₂ hD₂
  dsimp only at hrange
  have hlogdiv:=Real.logb_div (b:=Z) hX₂.ne' (zero_lt_one.trans_le hn₂).ne'
  rw [←hlogdiv] at hrange
  have hL0:0≤L:=by linarith
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,hrange.2.1,
    max_le hL0 (by linarith [hrange.1]),?_⟩
  rw [he₁,he₂]
  by_cases hd:length Z (X₁/((∏P∈D₁,P).absNorm:ℝ))+
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+z≤5*s.width/6
  · refine Or.inl ⟨hd,?_⟩
    have hkz:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*κ)
    linarith
  · obtain ⟨he,hbudget⟩:=CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets s.width (length Z X₁+length Z X₂) ell κ 0
      hell (by linarith) (by simpa only [sub_zero] using hlarge) (by linarith)
    have hlow:=CenteredMomentEnergyLiveClippingDefect.robust_reflected_low s.width (length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)))
      (Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))) ell z κ xi 0
      (max 0 (s.width-Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+xi))
      hM.le (length_nonneg Z _ hZ)
      (hd₁.trans hshort) hell hz hze (by linarith) he hbudget hxi (by norm_num) hM.le
      (by rw [←length_eq_max_log Z _ hZ hp₂];exact lt_of_not_ge hd) le_rfl
    exact Or.inr (CenteredMomentEnergyLiveClippingDefect.robust_reflected_low_admissible s.width xi 0 _ _ z κ
      (by norm_num) (by linarith) hlow.2.1 hlow.2.2)


end OAI.SevenEighths.Angular.NaturalUnbalanced

#print axioms OAI.SevenEighths.Angular.NaturalUnbalanced.divisor_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalUnbalanced.divisor_norm

#print axioms OAI.SevenEighths.Angular.NaturalUnbalanced.divided_scale_power
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalUnbalanced.divided_scale_power

#print axioms OAI.SevenEighths.Angular.NaturalUnbalanced.divisor_reflection_range
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalUnbalanced.divisor_reflection_range

#print axioms OAI.SevenEighths.Angular.NaturalUnbalanced.original_long_positive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalUnbalanced.original_long_positive

#print axioms OAI.SevenEighths.Angular.NaturalUnbalanced.actual_deleted_gates
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalUnbalanced.actual_deleted_gates
