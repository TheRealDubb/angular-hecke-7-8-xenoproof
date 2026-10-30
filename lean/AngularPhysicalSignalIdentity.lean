import AngularPhysicalSignal
import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity


namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical
namespace SevenEighths.Angular.PhysicalSignal
open HeckeFamily Continuation

private theorem line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

theorem signalMellin_eq_amplitude (χ : AngularCharacter) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (signal χ H c) c s = amplitude χ H s := by
  have hF := signalMellin_analytic (signal χ H c) a c
    (signal_locallyIntegrable χ H hH hb c) htop (signal_rapidDecayAtZero χ H hH hb c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (signal χ H c) c) {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (amplitude χ H) {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro z hz
    have hq := quotient_differentiableAt χ H hH ((le_max_right a 1).trans_lt hz)
    exact ((((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul hq).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y => signalMellin_eq_amplitude_on_line χ H hH hb c a ha htop y)

/-- The analytic conclusion for actual nonprincipal angular characters.
The low physical-probe estimate and the principal-signal comparison remain
the explicit hJ and herror premises. This is not an unconditional theorem. -/
theorem nonprincipal_nonzero_of_probe_bounds (χ : AngularCharacter)
    (hχ : χ.k≠0 ∨ χ.residue≠1) (H : ℂ→ℂ) (J : ℝ→ℂ)
    (β ω σ c : ℝ) (hβ : β≤1) (hω0 : 0<ω) (hω : ω<β-7/8) (hσ : 0<σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀s : ℂ,7/8<s.re → ‖H s-1‖≤1/2)
    (hJ : J =O[atTop] (fun x : ℝ=>x^(7/8+c+ω)))
    (herror : (fun x=>J x-signal χ H c x) =O[atTop]
      (fun x : ℝ=>x^(β+c-σ)))
    {ρ : ℂ} (hρ : β-Supremum.continuationMargin β ω σ<ρ.re) :
    FamilyContinuation.LFunction χ ρ≠0 := by
  let a := β-Supremum.continuationMargin β ω σ
  have ha2 : a<2 := by
    have hp := Supremum.continuationMargin_pos hω hσ
    dsimp [a]
    linarith
  have htop : signal χ H c =O[atTop] (fun x : ℝ=>x^(a+c)) := by
    have h := common_signal_bound_with_margin J (signal χ H c) β ω σ c hJ herror
    convert h using 1
    dsimp [a]
    ring_nf
  have hHd := hH.differentiableOn
  have hboundary : (7/8:ℝ)<a := Supremum.continuation_boundary_gt hω0
  have hregular : AnalyticOnNhd ℂ (PhysicalLogarithmicInput.regular χ)
      {s : ℂ | a<s.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt _)).2
    intro s hs
    change a<s.re at hs
    exact (PhysicalLogarithmicInput.regular_differentiableAt χ (by linarith)).differentiableWithinAt
  apply nonzero_of_common_signal β ω σ c hω0 (FamilyContinuation.LFunction χ)
    (PhysicalLogarithmicInput.regular χ) (fun _ : ℂ=>(1:ℂ)) H J (signal χ H c)
    hregular (by fun_prop) hH hb
    (signal_locallyIntegrable χ H hHd hb c) (signal_rapidDecayAtZero χ H hHd hb c)
    hJ herror _ hρ _ one_ne_zero
  · intro s hs
    have hs1 : 1<s.re := (le_max_right a 1).trans_lt hs
    rw [PhysicalLogarithmicInput.regular_eq_nonprincipal χ hχ,
      signalMellin_eq_amplitude χ H hHd hb c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [PhysicalReciprocal.reciprocal_eq_nonprincipal χ hχ]
    have hn := FamilyContinuation.LFunction_ne_zero χ s hs1
    field_simp
  · simp only [PhysicalLogarithmicInput.regular_eq_nonprincipal χ hχ,one_mul]

end SevenEighths.Angular.PhysicalSignal
end
end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalSignal.signalMellin_eq_amplitude

#print axioms OAI.SevenEighths.Angular.PhysicalSignal.nonprincipal_nonzero_of_probe_bounds
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalSignal.nonprincipal_nonzero_of_probe_bounds
