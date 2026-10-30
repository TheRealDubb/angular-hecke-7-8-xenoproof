import AngularPhysicalPrincipalRemainderScale
import OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace OAI.SevenEighths.Angular.PhysicalPrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary
open ProbePrincipalContours ProbePrincipalRemainderBounds
open PhysicalPrincipalProducts PhysicalPrincipalX
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma eventual_annulus_threshold {ι : Type*} (η : AngularCharacter) (J : Finset ι)
    (c : ℝ) (hc : 0<c) (ell : ι→ℝ) (hell : ∀j∈J,0<ell j) :
    ∃Z0 : ℝ,1≤Z0 ∧ ∀Z : ℝ,Z0≤Z→∀j∈J,
      480≤c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j) := by
  have hh : ∀ᶠZ : ℝ in atTop,∀j∈J,
      480≤c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j) := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    have ht := (tendsto_rpow_atTop (hell j hj)).const_mul_atTop hc
    exact (ht.eventually (eventually_ge_atTop 480)).and
      (ht.eventually (eventually_gt_atTop (Ideal.absNorm η.modulus:ℝ)))
  obtain ⟨Z0,hZ0⟩ := eventually_atTop.mp hh
  refine ⟨max 1 Z0,le_max_left _ _,?_⟩
  intro Z hZ
  exact hZ0 Z ((le_max_right _ _).trans hZ)

theorem source_remainders_power_bound {ι : Type*}
    (angularCap : ℕ) (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (hk : η.k≠0) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : (PhysicalZeroSupremum.beta angularCap)<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>PhysicalPrincipalMellin.sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (PhysicalDetectorHigh.globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-11/16+(13/16)*e-23/960)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤C*Z^(a-11/16-13/9600)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound angularCap η horder hk S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(ell j)) (fun _ _=>Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J ell hell Z a e hZ,source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

theorem source_remainders_strict_saving {ι : Type*}
    (angularCap : ℕ) (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (hk : η.k≠0) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : (PhysicalZeroSupremum.beta angularCap)+e∈Icc (7/8:ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>PhysicalPrincipalMellin.sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (PhysicalDetectorHigh.globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral ((PhysicalZeroSupremum.beta angularCap)+e) (fun s=>verticalIntegral (1/6+e)
      (fun z=>verticalIntegral (19/20) (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^((PhysicalZeroSupremum.beta angularCap)-11/16-17/48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral ((PhysicalZeroSupremum.beta angularCap)+e)
      (fun s=>verticalIntegral (33/200) (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^((PhysicalZeroSupremum.beta angularCap)-11/16-17/48000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound angularCap η horder hk S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 ((PhysicalZeroSupremum.beta angularCap)+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent (PhysicalZeroSupremum.beta angularCap) e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent (PhysicalZeroSupremum.beta angularCap) e hehi)) hC.le)


end OAI.SevenEighths.Angular.PhysicalPrincipalRemainderBounds

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalRemainderBounds.eventual_annulus_threshold

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalRemainderBounds.source_remainders_power_bound

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalRemainderBounds.source_remainders_strict_saving
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalRemainderBounds.source_remainders_strict_saving
