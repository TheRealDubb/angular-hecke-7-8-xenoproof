import AngularPhysicalDetectorHighCoefficient
import OAI.NumberTheory.DirichletL.Detector.Physical

/- Literal angular extension of the pinned original physical probe.
Generic calibration, spectral rows and Gauss sums are reused unchanged.
The global contour identity and detector bound are separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Angular.PhysicalDetectorProbe
noncomputable section
open scoped Classical BigOperators
open MeasureTheory
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow ProbePhysical
open InitialMeanSquare
local notation "O" => ActualEisensteinCubic.O

def targetMonoid (η : AngularCharacter) : O →* ℂ where
  toFun := η.elementCoeff
  map_one' := η.elementCoeff_one
  map_mul' := η.elementCoeff_mul

theorem targetMonoid_norm_le_one (η : AngularCharacter) (a : O) :
    ‖targetMonoid η a‖≤1 := η.norm_elementCoeff_le_one a

def rowCoefficient (η : AngularCharacter) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m : O) : O →* ℂ :=
  targetMonoid η * conjugateMonoid Xi * reciprocityPhaseMonoid s hs *
    (idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem rowCoefficient_apply (η : AngularCharacter) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    rowCoefficient η Xi s hs m a = η.elementCoeff a * star (Xi a) *
      sexticReciprocityPhase s a * idealRowHom m (Ideal.span {a}) := rfl

theorem rowCoefficient_apply_unit (η : AngularCharacter) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) (hXi : ‖Xi a‖ = 1) :
    rowCoefficient η Xi s hs m a = η.elementCoeff a * (Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) := by
  rw [rowCoefficient_apply]
  have hc : star (Xi a) = (Xi a)⁻¹ := (Complex.inv_eq_conj hXi).symm
  have hsym : sexticReciprocityPhase s a = sexticReciprocityPhase a s := by
    simp only [sexticReciprocityPhase, QuadraticAllOddCRT.quadraticRaySign_symm]
  rw [hc, hsym]

theorem rowCoefficient_norm_le_one (η : AngularCharacter) (Xi : O →* ℂ)
    (hXi : ∀ a, ‖Xi a‖ ≤ 1) (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    ‖rowCoefficient η Xi s hs m a‖ ≤ 1 := by
  rw [rowCoefficient_apply]
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (idealRowHom_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a)

def markedPhysicalProbe (η : AngularCharacter) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p ∈ C.excluded, ¬p ∣ s.val then
      let a := primaryGenerator s.val
      let ha := supported_primaryGenerator_ne_zero s.val s.property
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s / Y) * idealRowHom C.generator s.val /
        (C.tau * C.residueMonoid a * (Real.sqrt (elementNorm C.generator * q_s * X) : ℂ)) *
      ∑' m : O,
        C.residueMonoid m * (Real.sqrt q_s : ℂ)⁻¹ * sexticGauss a ha (-m) *
          W₀ (elementNorm m / (elementNorm C.generator * q_s * X)) *
          verticalIntegral 4 (fun t => (Z : ℂ) ^ t * Complex.exp (t ^ 2) *
            spectralRow C.excluded D (rowCoefficient η C.Xi a has m) t)
    else 0

def physicalProbe (η : AngularCharacter) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  markedPhysicalProbe η C 1 W₀ W₁ X Y Z

def slotProduct {K : ℕ} (p : Fin K → O) (J : Finset (Fin K)) : O := ∏ i ∈ J, p i

def compensatedTuple {K : ℕ} (η : AngularCharacter) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin K → O) (X Y Z : ℝ) : ℂ :=
  ProbeCompensation.tupleOperation p elementNorm (η.elementCoeff)
    (fun a => markedPhysicalProbe η C (Ideal.span {a}) W₀ W₁) X Y Z

@[simp] theorem elementNorm_one : elementNorm (1 : O) = 1 := by
  simp [elementNorm]

attribute [local irreducible] markedPhysicalProbe

theorem compensatedTuple_zero (η : AngularCharacter) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 0 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z = physicalProbe η C W₀ W₁ X Y Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_zero p elementNorm (η.elementCoeff)
    elementNorm_one (η.elementCoeff_one)]
  change markedPhysicalProbe η C (Ideal.span {(1 : O)}) W₀ W₁ X Y Z =
    markedPhysicalProbe η C 1 W₀ W₁ X Y Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]

theorem compensatedTuple_one (η : AngularCharacter) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 1 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z =
      star (η.elementCoeff (p 0)) *
        markedPhysicalProbe η C (Ideal.span {p 0}) W₀ W₁ X Y (Z * elementNorm (p 0)) -
      (elementNorm (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) *
        physicalProbe η C W₀ W₁ (X / elementNorm (p 0)) (Y / elementNorm (p 0)) Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_one p elementNorm (η.elementCoeff)
    elementNorm_one (η.elementCoeff_one)]
  change _ = _ - _ * markedPhysicalProbe η C 1 W₀ W₁ _ _ Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]

def compensatedPhysicalProbe {K : ℕ} (η : AngularCharacter) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (slotPrimes : Fin K → Finset O)
    (slotWindow : Fin K → ℝ → ℂ) (slotScale : Fin K → ℝ) (X Y Z : ℝ) : ℂ :=
  ∑ p : ((i : Fin K) → {a : O // a ∈ slotPrimes i}),
    (∏ i : Fin K, slotWindow i (elementNorm (p i).val / slotScale i)) *
      compensatedTuple η C W₀ W₁ (fun i => (p i).val) X Y Z


theorem targetMonoid_eq_checked_high (η : AngularCharacter) :
    targetMonoid η=(PhysicalDetectorHigh.targetMonoid η).toMonoidHom := rfl

end
end OAI.SevenEighths.Angular.PhysicalDetectorProbe

/- Source pins: Row.lean SHA256 94cd0a68ced17d2ad52c67c13af03a3d199568862ebe43fde2f9f0ed96949ce0; Physical.lean SHA256 324e33aaa6f25f99f984f75231e292d08d37ee971826d927b539861c326d5544 -/

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorProbe.rowCoefficient_norm_le_one

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorProbe.compensatedTuple_one

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorProbe.targetMonoid_eq_checked_high
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorProbe.targetMonoid_eq_checked_high
