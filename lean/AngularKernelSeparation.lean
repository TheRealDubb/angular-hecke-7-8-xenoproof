import AngularKernelSourceUniform
import OAI.NumberTheory.DirichletL.Reflection.KernelSource

/-! Fourier separation and finite contraction for the actual angular
kernel with the original four coordinate windows and reciprocal normalization.
No absolute values are introduced before the finite coefficient sum. -/
namespace OAI.CubicEisenstein.AngularKernelSeparation
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge SevenEighths.InverseKernelSourceUniform
open SevenEighths.InverseReflectedPhase
noncomputable section
universe u

theorem reflected_kernel_uniform_separation (order : ℕ) (a b : ℝ) (ha : 0<a)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter C QK QP Qn Qb
      (∀ k p n q : ℝ, 0<k → 0<p → 0<n → 0<q →
        (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n q i)) *
          AngularReflectionKernel.paperKernel order (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
            (C*n*q^3/(k^2*p^2)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (kernelCoordinateWeight (windows 0) (-2) QK t k *
            kernelCoordinateWeight (windows 1) (-2) QP t p *
            kernelDualWeight windows Qn Qb t n q) * AngularKernelSourceUniform.twistedDensity order U W θ R t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := AngularKernelSourceUniform.normTwistedSource_uniform_separation order
    a b ha windows kernelSlope M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  obtain ⟨he,hi,hm,hp⟩ := hsep θ _ hR
  refine ⟨?_,hi,hm,hp⟩
  intro k p n q hk hp hn hq
  rw [actual_annular_kernel_identity C QK QP Qn Qb k p n q hQK hQP hQn hQb hk hp hn hq]
  rw [he]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [kernel_mode_separation])


lemma reflected_density_integrable (order : ℕ) (U W : ℝ→ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (θ R : ℝ) (hR : 0<R) (J : ℕ)
    (hi : Integrable (fun t : ℝ => (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖)) :
    Integrable (AngularKernelSourceUniform.twistedDensity order U W θ R) := by
  have hm := (AngularKernelSourceUniform.twistedDensity_joint_stronglyMeasurable order U W hU a b ha hWs hW R hR).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable (fun t : ℝ => (θ,t)))
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg t]))



theorem reflected_finite_source_uniform (order : ℕ)
    (a b : ℝ) (ha : 0<a) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb r : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb → 0<r →
      let R := kernelCenter C QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (coeff : κ→ℂ) (k p n q : κ→ℝ),
        (∀ j ∈ source, 0<k j ∧ 0<p j ∧ 0<n j ∧ 0<q j) →
        (∑ j ∈ source, coeff j *
          ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (k j) (p j) (n j) (q j) i)) /
            ((r*Real.sqrt (n j)*q j:ℝ):ℂ) *
            AngularReflectionKernel.paperKernel order (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
              (C*n j*(q j)^3/((k j)^2*(p j)^2)))) =
        ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, AngularKernelSourceUniform.twistedDensity order U W θ R t *
            ∑ j ∈ source, coeff j *
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (k j)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (p j)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (n j) (q j))) ∧
      Integrable (AngularKernelSourceUniform.twistedDensity order U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖AngularKernelSourceUniform.twistedDensity order U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_kernel_uniform_separation order
    a b ha (reciprocalKernelWindows windows M) M hM
      (reciprocalKernelWindows_support windows M hwindows) W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb r hC hQK hQP hQn hQb hr
  obtain ⟨he,hi,hm,hp⟩ := hsep θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  have hdi := reflected_density_integrable order U W hUs.continuous.measurable
    a b ha hWsupport hW θ _ hR J hi
  refine ⟨?_,hdi,hi,hm,hp⟩
  intro κ source coeff k p n q hn
  apply kernel_finite_contraction source coeff _ _ hdi _
    (reciprocalKernelWindows windows M) QK QP Qn Qb k p n q
  intro j hj
  rw [reciprocal_source_window_identity windows M QK QP Qn Qb
    (k j) (p j) (n j) (q j) r hQn hQb (hn j hj).2.2.1 (hn j hj).2.2.2 hr]
  rw [mul_assoc,he (k j) (p j) (n j) (q j) (hn j hj).1 (hn j hj).2.1 (hn j hj).2.2.1 (hn j hj).2.2.2,
    Complex.ofReal_mul]
  ring


#print axioms reflected_finite_source_uniform
end
end OAI.CubicEisenstein.AngularKernelSeparation
