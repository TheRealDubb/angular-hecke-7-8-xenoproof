import AngularPhysicalPrincipalResidueBound
import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalizer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalPrincipalWindowResidue
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open PhysicalPrincipalProducts PhysicalPrincipalMellin PhysicalPrincipalResidue PhysicalSignal
open ProbePhysical ActualEisensteinCubic CompletedGauss

def residueWeights {κ : Type*} (W : κ → ℝ → ℝ) (scale : κ → ℝ)
    (j : κ) (p : PrimeIdeal) : ℝ :=
  W j ((Ideal.absNorm p.val : ℝ)/scale j) * (Ideal.absNorm p.val : ℝ)^(-(5/6 : ℝ))

theorem actual_window_residue {κ : Type*} (η : AngularCharacter) (S : Finset κ)
    (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (s : ℂ) :
    windowMultiplier η S T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      slotProduct S T (residueWeights W scale) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => PhysicalDetectorHigh.actualAPhase η (primaryGenerator p.val))
        (fun _ p => η.idealHom p.val) s := by
  exact window_at_residue η S T W scale s

theorem uniform_normalized_actual_window_residue {κ : Type*} (angularCap : ℕ)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E)
    {a : ℝ} (ha : 7/8<a) (ha2 : a≤2) (hβ : PhysicalZeroSupremum.beta angularCap<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤D ∧ ∀η : AngularCharacter,η.k.natAbs≤angularCap → η.k≠0 → ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0<a0 → 0<a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤P → 1440*P^(-(7/8 : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0<slotMass T (residueWeights W scale) j) → 1≤Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (1/6) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        PhysicalPrincipalMellin.sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (PhysicalDetectorHigh.globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(17/48 : ℝ)) Y Z (PhysicalDetectorHigh.globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D*((η.excludePrimes E hE.prime).modulus.absNorm:ℝ)^2*Z^(a-11/16)*P^(-(7/8 : ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := uniform_normalized_actual_source_bound angularCap E hE ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro η horder hk W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound η horder hk W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏p∈E,p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _


end OAI.SevenEighths.Angular.PhysicalPrincipalWindowResidue

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalWindowResidue.actual_window_residue

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalWindowResidue.uniform_normalized_actual_window_residue
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalWindowResidue.uniform_normalized_actual_window_residue
