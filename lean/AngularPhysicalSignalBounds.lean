import AngularPhysicalSignalShift
import AngularPhysicalSignalReciprocalGrowth

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
namespace OAI.SevenEighths.Angular.PhysicalSignalBounds
open PhysicalSignal Continuation

theorem contour_shift_left (angularCap : ℕ) (χ : AngularCharacter)
    (horder : χ.k.natAbs≤angularCap) (hnp : χ.k≠0 ∨ χ.residue≠1) (H : ℂ→ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀s : ℂ,7/8<s.re → ‖H s-1‖≤1/2)
    (c a : ℝ) (ha : (7/8:ℝ)<a) (ha2 : a≤2)
    (hbeta : PhysicalZeroSupremum.beta angularCap<a) {x : ℝ} (hx : 1≤x) :
    signal χ H c x=(1/(2*Real.pi):ℂ)*
      ∫y : ℝ,gaussianContourIntegrand (quotient χ H) c x ((a:ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := nonprincipal_polynomial_reciprocal_bound angularCap a hbeta
  exact PhysicalSignalShift.contour_shift_left angularCap χ horder H hH hb c a
    (C*(χ.modulus.absNorm:ℝ)^2) 2 ha ha2 hbeta (by positivity)
    (fun s hs _=>hbound χ horder hnp s hs) hx

/-- A common signal constant for all finite conductors at a fixed angular
cap and fixed line strictly right of the actual zero supremum. -/
theorem uniform_signal_bound_at_infinity (angularCap : ℕ) (c a : ℝ)
    (ha : (7/8:ℝ)<a) (ha2 : a≤2) (hbeta : PhysicalZeroSupremum.beta angularCap<a) :
    ∃D : ℝ,0≤D ∧ ∀χ : AngularCharacter,χ.k.natAbs≤angularCap →
      (χ.k≠0 ∨ χ.residue≠1) → ∀H : ℂ→ℂ,
      DifferentiableOn ℂ H {s : ℂ | 7/8<s.re} →
      (∀s : ℂ,7/8<s.re → ‖H s-1‖≤1/2) → ∀x : ℝ,1≤x →
      ‖signal χ H c x‖≤D*(χ.modulus.absNorm:ℝ)^2*x^(a+c) := by
  obtain ⟨C,hC,hbound⟩ := nonprincipal_polynomial_reciprocal_bound angularCap a hbeta
  let D := PhysicalSignalShift.infinityConstant a C 2
  have hD : 0≤D := by
    dsimp [D,PhysicalSignalShift.infinityConstant]
    have hi : 0≤∫y : ℝ,polynomialGaussian 2 y := integral_nonneg (fun y=>by
      unfold polynomialGaussian
      positivity)
    positivity
  refine ⟨D,hD,?_⟩
  intro χ horder hnp H hH hb x hx
  have hh := PhysicalSignalShift.signal_bound_at_infinity angularCap χ horder H hH hb c a
    (C*(χ.modulus.absNorm:ℝ)^2) 2 ha ha2 hbeta (by positivity)
    (fun s hs _=>hbound χ horder hnp s hs) hx
  convert hh using 1
  dsimp [D,PhysicalSignalShift.infinityConstant]
  ring

theorem signal_isBigO_atTop (angularCap : ℕ) (χ : AngularCharacter)
    (horder : χ.k.natAbs≤angularCap) (hnp : χ.k≠0 ∨ χ.residue≠1) (H : ℂ→ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀s : ℂ,7/8<s.re → ‖H s-1‖≤1/2)
    (c a : ℝ) (ha : (7/8:ℝ)<a) (ha2 : a≤2)
    (hbeta : PhysicalZeroSupremum.beta angularCap<a) :
    signal χ H c =O[atTop] (fun x : ℝ=>x^(a+c)) := by
  obtain ⟨D,hD,hbound⟩ := uniform_signal_bound_at_infinity angularCap c a ha ha2 hbeta
  apply IsBigO.of_bound (D*(χ.modulus.absNorm:ℝ)^2)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤x) (a+c))]
    using hbound χ horder hnp H hH hb x hx

end OAI.SevenEighths.Angular.PhysicalSignalBounds

#print axioms OAI.SevenEighths.Angular.PhysicalSignalBounds.contour_shift_left

#print axioms OAI.SevenEighths.Angular.PhysicalSignalBounds.uniform_signal_bound_at_infinity

#print axioms OAI.SevenEighths.Angular.PhysicalSignalBounds.signal_isBigO_atTop
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalSignalBounds.signal_isBigO_atTop
