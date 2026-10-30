import AngularPhysicalReciprocalLocal
import AngularPhysicalDetectorPrimitive
import AngularPhysicalDetectorZeros
noncomputable section
open scoped Classical Topology
open Set Metric
namespace OAI.SevenEighths.Angular.PhysicalDetectorControl
open FamilyContinuation PrimitiveReduction PhysicalLogarithmicInput PhysicalLogarithmic
open PhysicalReciprocal (presentationComplexity)
open HeckeDeletionBounds
theorem original_disk_control (n:ℕ) (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : AngularCharacter), χ.k.natAbs≤n → (χ.k≠0 ∨ χ.residue≠1) → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction χ z‖ + ‖PhysicalReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := PhysicalLogarithmic.disk_control n e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := DeletionBounds.factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
  intro χ hn aNonprincipal a t ha ha' hzero z hz
  let ψ:=primitive χ
  have hp:=primitive_isPrimitive χ
  have hψ:=NaturalPrimitive.primitive_nonprincipal χ aNonprincipal
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hidentity (w:ℂ):LFunction χ w=LFunction ψ w*factors χ w :=
    PhysicalDetectorPrimitive.nonprincipal_primitive_identity χ aNonprincipal w
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [hidentity w, hh, zero_mul]
  have hbound := (hprimitive ψ hn hp a t ha ha' hzeroψ).1 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  change ‖factors χ z‖+‖(factors χ z)⁻¹‖≤Cd*((radical χ.modulus).absNorm:ℝ)^ε at hdel
  have hL : LFunction χ z = LFunction ψ z*factors χ z :=
    hidentity z
  have hR : PhysicalReciprocal.reciprocal χ z =
      (LFunction ψ z)⁻¹*(factors χ z)⁻¹ := by
    rw [PhysicalReciprocal.reciprocal_eq_nonprincipal χ aNonprincipal,hL,mul_inv_rev]
    ring
  have hdel1 : ‖factors χ z‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ z)⁻¹)]
  have hdel2 : ‖(factors χ z)⁻¹‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast PrimitiveReduction.norm_le χ
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖LFunction ψ z‖+‖(LFunction ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (LFunction ψ z))
      have h2 := mul_le_mul_of_nonneg_left hdel2 (norm_nonneg ((LFunction ψ z)⁻¹))
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_original_control (n:ℕ) (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → AngularCharacter) (horder:∀j,(χ j).k.natAbs≤n)
      (hχ : ∀ j, (χ j).k≠0 ∨ (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      PhysicalDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction (χ j) z‖+‖PhysicalReciprocal.reciprocal (χ j) z‖ ≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_disk_control n e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ horder hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (horder j) (hχ j) a t (by linarith) ha'
    (fun w hw => PhysicalDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

end OAI.SevenEighths.Angular.PhysicalDetectorControl

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorControl.original_disk_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorControl.original_disk_control

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorControl.buffered_original_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorControl.buffered_original_control
