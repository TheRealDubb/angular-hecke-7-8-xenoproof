import AngularPhysicalFixedWitnesses
import AngularPhysicalDetectorActualSignalContraction
import AngularPhysicalLowNormalized
import AngularPhysicalAnalyticDeletion
import AngularPhysicalCapClosure
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource

/- Assembly on the same actual physical probe, slots and ray normalizer.
The positive margin is chosen before the target character. Constants and
eventual thresholds in the two Big-O estimates may depend on that target.
No finite-order substitution is made for a nonzero angular character. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2800000
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter Asymptotics
namespace OAI.SevenEighths.Angular.PhysicalFinalAssembly
open PhysicalDetectorHigh PhysicalFixedWitnesses PhysicalZeroSupremum
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => ActualEisensteinCubic.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O⧸M)]
    (H : Subgroup (O⧸M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (w : ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : AngularCharacter) (Z : ℝ) : ℂ :=
  let Y := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
  PhysicalDetectorProbe.compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun _ y=>(w y:ℂ)) Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights (fun _=>w) Y)) : ℂ))

theorem negative_order_improvement : PhysicalCapClosure.NegativeOrderImprovement := by
  intro n hn hbeta
  let lowLoss : ℝ := (beta n-7/8)/2
  have hlowLoss0 : 0<lowLoss := by dsimp [lowLoss];linarith
  have hlowLoss : lowLoss<beta n-7/8 := by dsimp [lowLoss];linarith
  obtain ⟨p,_hpgap⟩ := exists_actual_retained_parameters lowLoss hlowLoss0
  have he : 0<p.e := p.early_conditions.2.2.2.2.1
  have hsave : 0<actualSignalSaving p := (actual_principal_signal_budget p).2.2.1
  let δ := Supremum.continuationMargin (beta n) lowLoss (actualSignalSaving p)
  have hδ : 0<δ := Supremum.continuationMargin_pos hlowLoss hsave
  obtain ⟨S,hbad,hS,hfirst,hmax⟩ := Parameters.exists_fixed_source p.e he
    CanonicalQuadraticSieve.fixedBadPrimes Parameters.fixed_bad_primes_prime
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨w,W,hw,hcompact,hsupp,htsupport,hwb,hwne,hcast,hWne,hWs,hWr,hWp⟩ :=
    Parameters.exists_fixed_probe_window
  obtain ⟨Phi,bPhi,hbPhi,hsPhi,hpPhi,hone⟩ := exists_radial_majorant
  have hWopen : Function.support (W:ℝ→ℂ)⊆Ioo (1:ℝ) 2 := by
    intro x hx
    apply hsupp
    intro hz
    exact hx (by rw [hcast,hz];simp)
  have hWbound : ∀x,‖W x‖≤1 := by
    intro x
    rw [hcast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwb x).1]
    exact (hwb x).2
  have hWR : (fun t=>(W t).re)=w := by
    funext t
    rw [hcast,Complex.ofReal_re]
  have hWC : (W:ℝ→ℂ)=(fun t=>(w t:ℂ)) := funext hcast
  have hWfnne : (W:ℝ→ℂ)≠0 := by
    intro hz
    apply hWne
    ext x
    exact congrFun hz x
  have hhigh := actual_physical_signal_contraction rayModulus ⊤ le_top n hn p hbeta.le
    1 bPhi 1 (by norm_num) hbPhi (by norm_num) S hS hfirst hmax hbad
    rayModulus_le_mask rayModulus_ne_top rayModulus_le_72
    W hWopen (W.smooth (⊤:ℕ∞)) hWbound hWr hWp hWfnne Phi hsPhi hpPhi hone
    w hw hcompact htsupport (fun x=>(hwb x).1) hwne
    1 2 1 (by norm_num) (by norm_num) (by norm_num) hsupp (fun x=>(hwb x).2)
    W W 1 2 1 2 (by norm_num) (by norm_num) hWs hWs hWr hWr hWp hWp hWne hWne
  rcases p.slot_conditions with ⟨_hN,_heven,_hrmin,hellinj,hellsum,hslots⟩
  have hlow := PhysicalLow.original_normalized_compensatedPhysicalProbe_low rayModulus ⊤ le_top
    S hS hmax 1 2 1 lowLoss (by norm_num) (by norm_num) hlowLoss0 p.ell
    (fun j=>(hslots j).1) hellinj hellsum (fun _=>w) (fun _=>hw) (fun _=>hcompact)
    (fun _=>hsupp) (fun _=>hwb) (fun _=>hwne)
    W W 1 2 1 2 (by norm_num) (by norm_num) hWs hWs hWr hWr hWp hWp hWne hWne
  refine ⟨δ,hδ,?_⟩
  intro η hk s hs
  have hk0 : η.k≠0 := by
    rw [hk]
    exact neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))
  let J := normalizedProbe rayModulus ⊤ S hmax p.ell w W W η
  have hJ : J=O[atTop](fun Z : ℝ=>Z^(7/8+(-11/16)+lowLoss)) := by
    obtain ⟨C,hC,hbound⟩ := hlow η n hk hn
    apply ProbeFinalAssembly.isBigO_rpow_of_eventual_norm_bound
    refine ⟨C,hC,?_⟩
    filter_upwards [hbound] with Z hZ
    simpa only [J,normalizedProbe,show (7/8:ℝ)+(-11/16)=3/16 by norm_num] using hZ.2
  have herror : (fun Z=>J Z-PhysicalSignal.signal (η.excludePrimes S hS.prime)
        (PhysicalPrincipalResidue.sourceCorrection η S) (-11/16) Z)
      =O[atTop](fun Z : ℝ=>Z^(beta n+(-11/16)-actualSignalSaving p)) := by
    obtain ⟨C,hC,hbound⟩ := hhigh η hk
    apply ProbeFinalAssembly.isBigO_rpow_of_eventual_norm_bound
    refine ⟨C,hC,?_⟩
    filter_upwards [hbound] with Z hZ
    simpa only [J,normalizedProbe,hWC,hWR,Complex.ofReal_re,sub_eq_add_neg,neg_div] using hZ.2
  have hfree : FamilyContinuation.LFunction (η.excludePrimes S hS.prime) s≠0 :=
    PhysicalSignal.nonprincipal_nonzero_of_probe_bounds (η.excludePrimes S hS.prime)
      (Or.inl hk0) (PhysicalPrincipalResidue.sourceCorrection η S) J
      (beta n) lowLoss (actualSignalSaving p) (-11/16) (beta_le_one n) hlowLoss0 hlowLoss hsave
      ((PhysicalPrincipalResidue.sourceCorrection_differentiable η S hS).analyticOnNhd
        (Complex.isOpen_re_gt _))
      (PhysicalPrincipalResidue.sourceCorrection_bound η S hS) hJ herror hs
  have hspos : 0<s.re := by
    have hb : (7/8:ℝ)<beta n-δ := Supremum.continuation_boundary_gt hlowLoss0
    linarith
  exact PhysicalAnalyticDeletion.nonzero_of_excluded η hk0 S hS.prime hspos hfree

/-- The actual Eisenstein angular L-function, with the sole principal pole
excluded. No claim about the Gaussian angular family is made here. -/
theorem LFunction_ne_zero_of_seven_eighths_lt_re (χ : AngularCharacter) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : χ.k=0 → χ.residue=1 → s≠1) :
    FamilyContinuation.LFunction χ s≠0 :=
  PhysicalCapClosure.nonzero_of_negative_order_improvement negative_order_improvement χ s hs hpole

end OAI.SevenEighths.Angular.PhysicalFinalAssembly
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.negative_order_improvement
#print axioms OAI.SevenEighths.Angular.PhysicalFinalAssembly.LFunction_ne_zero_of_seven_eighths_lt_re
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalFinalAssembly.LFunction_ne_zero_of_seven_eighths_lt_re
