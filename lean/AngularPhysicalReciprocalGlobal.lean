import AngularPhysicalDetectorControl
import AngularPhysicalZeroSupremum
import OAI.NumberTheory.DirichletL.Hecke.DyadicReflectedControl

/- Global nonprincipal reciprocal growth relative to the actual fixed-cap
zero supremum. No numerical zero-free bound or seed is assumed. The disk
nonvanishing premise is discharged by the definition of that supremum.
The principal character is deliberately outside this statement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical Topology
open Set Metric
namespace OAI.SevenEighths.Angular.PhysicalReciprocal

lemma presentationComplexity_ge_one (χ : AngularCharacter) (t : ℝ) :
    1 ≤ presentationComplexity χ t := by
  have hr := HeckeDyadic.radical_norm_ge_one χ.modulus
  have hq := PhysicalLogarithmic.modulus_norm_ge_one χ
  have ht : 1 ≤ (3+|t|)^2 := by nlinarith [abs_nonneg t]
  have hc : 1 ≤ PhysicalLogarithmic.complexity χ t := by
    unfold PhysicalLogarithmic.complexity
    nlinarith [mul_le_mul hq ht (by positivity : (0:ℝ)≤1) (by positivity : (0:ℝ)≤(χ.modulus.absNorm:ℝ))]
  exact one_le_mul_of_one_le_of_one_le hr hc

theorem nonprincipal_reciprocal_subpower (n : ℕ) (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀χ : AngularCharacter,χ.k.natAbs≤n →
      (χ.k≠0 ∨ χ.residue≠1) → ∀z : ℂ,
      PhysicalZeroSupremum.beta n+8*e≤z.re →
      ‖reciprocal χ z‖≤C*(presentationComplexity χ z.im)^ε := by
  obtain ⟨D,hD,hcontrol⟩ := PhysicalDetectorControl.original_disk_control n e ε he he' hε
  let B : ℝ := HeckeReciprocalBound.bound 2
  have hB : 0≤B := by dsimp [B,HeckeReciprocalBound.bound];positivity
  refine ⟨D+B,by linarith,?_⟩
  intro χ horder hnp z hz
  have hp : 1≤(presentationComplexity χ z.im)^ε :=
    Real.one_le_rpow (presentationComplexity_ge_one χ z.im) hε.le
  by_cases hright : 2≤z.re
  · have hb : ‖reciprocal χ z‖≤B := reciprocal_norm_le χ (by norm_num) hright
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_left hp hB
    calc
      B ≤ B*(presentationComplexity χ z.im)^ε := by simpa using hm
      _ ≤ (D+B)*(presentationComplexity χ z.im)^ε := by gcongr;linarith
  · have hz2 : z.re≤2 := le_of_lt (lt_of_not_ge hright)
    have hzero : ∀w∈ball ((2:ℂ)+z.im*Complex.I)
        (2-PhysicalZeroSupremum.beta n-2*e),FamilyContinuation.LFunction χ w≠0 := by
      intro w hw
      have hwr := LogarithmicControl.disk_re_gt hw
      apply PhysicalZeroSupremum.LFunction_ne_zero_of_beta_lt n χ horder (by linarith)
      intro hk hr
      rcases hnp with hnp|hnp
      · exact False.elim (hnp hk)
      · exact False.elim (hnp hr)
    have hmem : z∈closedBall ((2:ℂ)+z.im*Complex.I)
        (2-PhysicalZeroSupremum.beta n-6*e) := by
      rw [mem_closedBall,dist_eq_norm]
      have hid : z-((2:ℂ)+z.im*Complex.I)=((z.re-2:ℝ):ℂ) := by
        apply Complex.ext <;> simp
      rw [hid,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      linarith
    have hd := hcontrol χ horder hnp (PhysicalZeroSupremum.beta n) z.im
      (PhysicalZeroSupremum.half_le_beta n) (PhysicalZeroSupremum.beta_le_one n) hzero z hmem
    apply (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hd).trans
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end OAI.SevenEighths.Angular.PhysicalReciprocal

#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.presentationComplexity_ge_one
#print axioms OAI.SevenEighths.Angular.PhysicalReciprocal.nonprincipal_reciprocal_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalReciprocal.nonprincipal_reciprocal_subpower
