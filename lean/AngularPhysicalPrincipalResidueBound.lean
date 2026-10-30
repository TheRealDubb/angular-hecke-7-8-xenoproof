import AngularPhysicalPrincipalResidueNormalization
import AngularPhysicalPrincipalMellin
import AngularPhysicalPrincipalProducts
import AngularPrimeDeletion
import AngularPhysicalIdealBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalPrincipalResidue
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbePhysical CompletedGauss PhysicalSignal PhysicalPrincipalSignal
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {κ ι : Type*}

def sourceCorrection (η : AngularCharacter) (E : Finset Id) (s : ℂ) : ℂ :=
  PhysicalDetectorHigh.globalClosedCorrection η E s 1 (1/6)

theorem sourceCorrection_differentiable (η : AngularCharacter) (E : Finset Id)
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ|7/8<s.re} := by
  apply (PhysicalDetectorHigh.remainder_globalClosedCorrection_analytic_x η E hE.tail 1 (1/6)
    (by norm_num) (by norm_num)).differentiableOn.mono
  intro s hs
  exact PhysicalDetectorHigh.theta_bounds.2.trans hs

theorem sourceCorrection_bound (η : AngularCharacter) (E : Finset Id)
    (hE : SourceExclusions E) (s : ℂ) (hs : 7/8<s.re) :
    ‖sourceCorrection η E s-1‖≤1/2 :=
  PhysicalDetectorHigh.remainder_globalClosedCorrection_bound η E hE.tail s 1 (1/6)
    (PhysicalDetectorHigh.theta_bounds.2.trans hs).le (by norm_num) (by norm_num)

theorem uniform_normalized_actual_source_bound (angularCap : ℕ) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) {a : ℝ}
    (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : PhysicalZeroSupremum.beta angularCap < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀η : AngularCharacter,η.k.natAbs≤angularCap → η.k≠0 → ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(7/8 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => PhysicalDetectorHigh.actualAPhase η (primaryGenerator p.val)) (fun _ p => η.idealHom p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        PhysicalPrincipalMellin.sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (PhysicalDetectorHigh.globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(17/48 : ℝ)) Y Z (PhysicalDetectorHigh.globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * ((η.excludePrimes E hE.prime).modulus.absNorm:ℝ)^2 * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hall⟩ := PhysicalPrincipalSignal.uniform_slotResidue_bound
    (ι := PrimeIdeal) angularCap a ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro η horder hk
  have hb := hall (η.excludePrimes E hE.prime)
    (by simpa only [AngularCharacter.excludePrimes_k] using horder)
    (Or.inl (by simpa only [AngularCharacter.excludePrimes_k] using hk))
    (sourceCorrection η E) (sourceCorrection_differentiable η E hE) (sourceCorrection_bound η E hE)
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (PhysicalDetectorHigh.globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => PhysicalDetectorHigh.actualAPhase η (primaryGenerator p.val))
    (fun _ p => η.idealHom p.val) hc hmass hB
  have hslots : SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => PhysicalDetectorHigh.actualAPhase η (primaryGenerator p.val)) (fun _ p => η.idealHom p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => PhysicalDetectorHigh.actualAPhase_norm_le_one η _,
      fun j hj p hp => AngularCharacter.norm_idealHom_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => PhysicalDetectorHigh.actualAPhase η (primaryGenerator p.val)) (fun _ p => η.idealHom p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (by linarith) (PhysicalDetectorHigh.globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => PhysicalDetectorHigh.actualAPhase η (primaryGenerator p.val))
      (fun _ p => η.idealHom p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2


end OAI.SevenEighths.Angular.PhysicalPrincipalResidue

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalResidue.sourceCorrection_differentiable

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalResidue.sourceCorrection_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalResidue.uniform_normalized_actual_source_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalResidue.uniform_normalized_actual_source_bound
