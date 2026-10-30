import AngularPhysicalSignalBounds
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace OAI.SevenEighths.Angular.PhysicalPrincipalSignal
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation PhysicalSignal
open PrincipalSignalComparison
variable {κ ι : Type*}

theorem raw_inverse_ae_reciprocal (χ : AngularCharacter) (a : ℝ) (ha : 0<a) :
    (fun t : ℝ => (FamilyContinuation.LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => PhysicalReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (PhysicalReciprocal.reciprocal_eq_inv χ ((a:ℂ)+t*I) (by simpa using ha) ?_).symm
  intro _ _ h
  exact ht (by simpa using congrArg Complex.im h)

theorem raw_quotient_integral_eq (χ : AngularCharacter) (a : ℝ) (ha : 0<a) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / FamilyContinuation.LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * PhysicalReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a ha] with t ht
  simp only [div_eq_mul_inv, ht]

def slotResidue (χ : AngularCharacter) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
      H ((a : ℂ)+t*I) / FamilyContinuation.LFunction χ ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I)

theorem slotResidue_eq_reciprocal (χ : AngularCharacter) (H : ℂ → ℂ) (a Z : ℝ) (ha : 0<a)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a ha] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

def kernel (χ : AngularCharacter) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I)

def kernelEnvelope (a C Z : ℝ) : ℝ :=
  Z^(a-11/16) * Real.exp ((a-5/6)^2) * ((3/2)*C)

theorem kernel_continuous (angularCap : ℕ) (χ : AngularCharacter) (horder : χ.k.natAbs≤angularCap) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    {a Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : PhysicalZeroSupremum.beta angularCap < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (PhysicalSignalShift.quotient_holomorphic angularCap χ horder H hH ha hβ) (-11/16) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound (χ : AngularCharacter) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖PhysicalReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := PhysicalSignalShift.quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-11/16))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable (angularCap : ℕ) (χ : AngularCharacter) (horder : χ.k.natAbs≤angularCap) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : PhysicalZeroSupremum.beta angularCap < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖PhysicalReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (kernel_continuous angularCap χ horder H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem slotResidue_bound_of_reciprocal_bound (angularCap : ℕ) (χ : AngularCharacter) (horder : χ.k.natAbs≤angularCap) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : PhysicalZeroSupremum.beta angularCap < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖PhysicalReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
        (PhysicalSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := kernel_integrable angularCap χ horder H hH hb ha ha2 hβ hC hZ0 hR
  have hc := slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [slotResidue_eq_reciprocal χ H a Z (by linarith) S T w Q A η,
      PhysicalSignalShift.contour_shift_left angularCap χ horder H hH hb (-11/16) a C 2 ha ha2 hβ hC (fun s hs _=>hR s hs) hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H a Z t * _ - kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(7/8 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(7/8 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(7/8 : ℝ))) :=
        mul_le_mul (kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(7/8 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold kernelEnvelope PhysicalSignalShift.infinityConstant
  ring_nf

theorem raw_slot_integrable (χ : AngularCharacter) (H : ℂ → ℂ) (a Z : ℝ) (ha : 0<a)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / FamilyContinuation.LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a ha] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

/-- One slot-error constant before the actual target and its finite
conductor. The reciprocal supplier is proved for the actual angular family;
the sharp slot hypotheses remain explicit. -/
theorem uniform_slotResidue_bound (angularCap : ℕ) (a : ℝ)
    (ha : (7/8:ℝ)<a) (ha2 : a≤2) (hbeta : PhysicalZeroSupremum.beta angularCap<a)
    (S : Finset κ) :
    ∃D : ℝ,0≤D ∧ ∀χ : AngularCharacter,χ.k.natAbs≤angularCap →
      (χ.k≠0 ∨ χ.residue≠1) → ∀H : ℂ→ℂ,
      DifferentiableOn ℂ H {s : ℂ|7/8<s.re} →
      (∀s : ℂ,7/8<s.re → ‖H s-1‖≤1/2) →
      ∀(T : κ→Finset ι)(w Q : κ→ι→ℝ)(A eta : κ→ι→ℂ)(P Z : ℝ),
      SlotBounds S T w Q A eta P → 1≤Z →
      Integrable (fun t : ℝ=>kernel χ H a Z t*slotRatio S T w Q A eta ((a:ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A eta-signal χ H (-11/16) Z‖≤
        D*(χ.modulus.absNorm:ℝ)^2*Z^(a-11/16)*P^(-(7/8:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := PhysicalSignalBounds.nonprincipal_polynomial_reciprocal_bound
    angularCap a hbeta
  let D := PhysicalSignalShift.infinityConstant a C 2*slotErrorConstant S
  have hD : 0≤D := by
    have hi : 0≤∫t : ℝ,polynomialGaussian 2 t := integral_nonneg (polynomialGaussian_nonneg 2)
    dsimp [D,PhysicalSignalShift.infinityConstant,slotErrorConstant]
    positivity
  refine ⟨D,hD,?_⟩
  intro χ horder hnp H hH hb T w Q A eta P Z h hZ
  have hh := slotResidue_bound_of_reciprocal_bound angularCap χ horder H hH hb
    ha ha2 hbeta (show 0≤C*(χ.modulus.absNorm:ℝ)^2 by positivity)
    (fun s hs=>hbound χ horder hnp s hs) S T w Q A eta h hZ
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1
  dsimp [D,PhysicalSignalShift.infinityConstant]
  ring

end OAI.SevenEighths.Angular.PhysicalPrincipalSignal

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.raw_inverse_ae_reciprocal

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.raw_quotient_integral_eq

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.slotResidue_eq_reciprocal

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.kernel_continuous

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.kernel_norm_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.kernel_integrable

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.slotResidue_bound_of_reciprocal_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.raw_slot_integrable

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalSignal.uniform_slotResidue_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalSignal.uniform_slotResidue_bound
