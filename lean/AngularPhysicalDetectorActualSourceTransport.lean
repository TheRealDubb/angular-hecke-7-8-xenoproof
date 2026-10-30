import AngularPhysicalDetectorActualWZTransport
import AngularPhysicalDetectorActualXShift

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CubicEisenstein ProbePhysical ProbeMellinBoundary
open HeckeFamily HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

open Filter
open scoped Topology
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions
  marked_firstTail FirstTail selectedFirstBound selectedFirstBound_nonneg
  calibrated_row_nonprincipal calibrated_numerator_first_growth)

private lemma height_integral_wzx (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫z : ℝ,∫x : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod_symm _ hw

theorem continuedRowOnLines_x_transport {K : ℕ}
    (l r υ ξ : ℝ) (hl : 2≤l) (hr3 : r≤3) (hlr : l≤r)
    (hυ : (1/2:ℝ)≤υ) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z l υ ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z r υ ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : l≤q) (hq3 : q≤3) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z q υ ξ) heightMeasure :=
    continuedPhysicalRowKernel_right_integrable q υ ξ (hl.trans hq) hq3 (by linarith) hξ
      S hS hmax hfirst P hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wzx _ (hi l le_rfl (hlr.trans hr3)),height_integral_wzx _ (hi r hlr hr3)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  exact right_x_integral_eq S hS hfirst hmax P hPS η u hu W0 W1 X Y Z hZ
    ((υ:ℂ)+tw*I) ((ξ:ℂ)+tz*I) l r hlr hl hr3 (by simpa using hυ) (by simpa using hξ)

theorem rowIntegral_source_lines {K : ℕ}
    (σ υ r : ℝ) (hσ : 2≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi := continuedPhysicalRowKernel_right_integrable σ υ r hσ hσ3 (by linarith) hr
    S hS hmax hfirst P hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_wz_transport S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ 2 hυ hυ3 (by norm_num) le_rfl
  have hz : (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure := by
    by_cases hr2 : r≤2
    · exact continuedRowOnLines_z_transport 3 υ r 2 (by norm_num) le_rfl hυ hr hr2
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    · exact (continuedRowOnLines_z_transport 3 υ 2 r (by norm_num) le_rfl hυ (by norm_num) (le_of_not_ge hr2)
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).symm
  have hx := continuedRowOnLines_x_transport σ 3 υ r hσ le_rfl hσ3 hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨hi,hphysical.trans (by rw [hx,hz])⟩


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedRowOnLines_x_transport

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowIntegral_source_lines
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowIntegral_source_lines
