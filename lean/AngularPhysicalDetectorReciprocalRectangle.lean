import AngularPhysicalDetectorBuffered
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Topology
open Set Metric
namespace OAI.SevenEighths.Angular.PhysicalDetectorControl
open PhysicalLogarithmic
open PhysicalReciprocal (presentationComplexity)
theorem buffered_rectangle_reciprocal_bound (angularOrder : ℕ) (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→AngularCharacter)
      (horder : ∀j,(χ j).k.natAbs≤angularOrder)
      (hnp : ∀j,(χ j).k≠0 ∨ (χ j).residue≠1)
      (T a H : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      H≤(3*i+2:ℕ)*T → PhysicalDetectorZeros.zeroMaximum χ hnp (3*(i+1:ℕ)*T)<a+2*e →
      ∀j z,a+16*e≤z.re → z.re≤2 → |z.im|≤H →
        ‖PhysicalReciprocal.reciprocal (χ j) z‖≤C*(presentationComplexity (χ j) H)^ε := by
  obtain ⟨C,hC,hbound⟩ := buffered_original_control angularOrder e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ horder hnp T a H i hT ha ha1 hHT hmax j z hzl hzr hzi
  have hz : z∈closedBall ((2:ℂ)+z.im*Complex.I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2:ℂ)+z.im*Complex.I)=((z.re-2:ℝ):ℂ) := by apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hb := hbound χ horder hnp T a i hT ha ha1 hmax j z.im (hzi.trans hHT) z hz
  have hc : presentationComplexity (χ j) z.im≤presentationComplexity (χ j) H := by
    unfold presentationComplexity complexity
    have hH : 0≤H := (abs_nonneg _).trans hzi
    rw [abs_of_nonneg hH]
    gcongr
  have hnonneg : 0≤presentationComplexity (χ j) z.im := by
    unfold presentationComplexity complexity
    positivity
  apply (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hb).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnonneg hc hε.le) hC.le


end OAI.SevenEighths.Angular.PhysicalDetectorControl

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorControl.buffered_rectangle_reciprocal_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorControl.buffered_rectangle_reciprocal_bound
