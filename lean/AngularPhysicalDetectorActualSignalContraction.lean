import AngularPhysicalPrincipalNormalized
import AngularPhysicalDetectorActualSignalBudget
import AngularPhysicalDetectorActualPhysicalContraction
import AngularPhysicalDetectorActualRetainedContraction
import AngularPhysicalDetectorActualCanonicalCubeReduction
import AngularPhysicalDetectorActualPhysicalJoinBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2600000
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (rowNorm FirstTail rowBand mem_rowBand)
open HeckeFamily ProbePhysical ProbeMellinBoundary ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

/-- Actual physical probe-to-signal error, with a positive saving fixed
before the target. The magnitude constant here may depend on the target.
This supplies the signal-error side only; the physical low bound and the
family-supremum contradiction are not conclusions of this theorem. -/
theorem actual_physical_signal_contraction
    (angularOrder : ℕ) (horder : 0<angularOrder) (p : ActualRetainedParameters)
    (hbeta : (7/8:ℝ)≤PhysicalZeroSupremum.beta angularOrder)
    (A bPhi ceiling : ℝ) (hA : 0≤A) (hbPhi : 2≤bPhi) (hceiling : 0<ceiling)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*p.e) S)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (hMmask : M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask})
    (hMt : M≠⊤) (hM72 : M≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (hWs : Function.support W⊆Ioo (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (hWB : ∀t,‖W t‖≤A)
    (hWreal : ∀t,(W t).im=0) (hWpos : ∀t,0≤(W t).re) (hWne : W≠0)
    (Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (hone : ∀x∈Icc (0:ℝ) 1,Phi x=1)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (alo bhi B : ℝ) (halo : 0<alo) (hab : alo≤bhi) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo alo bhi) (hφB : ∀y,φ y≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀t,(W0 t).im=0) (hr1 : ∀t,(W1 t).im=0)
    (hp0 : ∀t,0≤(W0 t).re) (hp1 : ∀t,0≤(W1 t).re) (hn0 : W0≠0) (hn1 : W1≠0)
:
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀eta : AngularCharacter,eta.k= -(angularOrder:ℤ) →
      ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let Y : Fin p.N→ℝ := fun j=>Z^(p.ell j)
      let T : Fin p.N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
      normer≠0 ∧
        ‖PhysicalDetectorProbe.compensatedPhysicalProbe eta (calibrationForSet S hmax) W0 W1
            (fun j=>canonicalSlotSupport (T j)) (fun _=>W) Y (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
          PhysicalSignal.signal (eta.excludePrimes S hS.prime)
            (PhysicalPrincipalResidue.sourceCorrection eta S) (-11/16) Z‖≤
          C*Z^(PhysicalZeroSupremum.beta angularOrder-11/16-actualSignalSaving p) := by
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Cd,hCd,hdet⟩ := actual_conductor_uniform_physical_contraction
    M H hH angularOrder horder p hbeta A bPhi ceiling hA hbPhi hceiling S hS hfirst hmax hbad
    hMmask hMt hM72 W hWs hW hWB hWreal hWpos hWne Phi hsPhi hpPhi hone
    φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  rcases p.slot_conditions with ⟨hN,heven,hrmin,hellinj,hellsum,hslots⟩
  rcases actual_principal_signal_budget p with ⟨he,hehi,hsave,hsavele,hrem,hslot⟩
  let WR : ℝ→ℝ := fun t=>(W t).re
  have hWR : ContDiff ℝ ∞ WR := Complex.reCLM.contDiff.comp hW
  have hWRs : Function.support WR⊆Ioo (1:ℝ) 2 := by
    intro t ht
    apply hWs
    intro hw
    exact ht (by dsimp [WR];rw [hw];simp)
  have hWRc : HasCompactSupport WR := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1:ℝ) 2))
    intro x hx
    by_contra h
    exact hx ((hWRs.trans Ioo_subset_Icc_self) h)
  have hWRne : WR≠0 := by
    intro hzero
    apply hWne
    funext t
    apply Complex.ext
    · have hh := congrFun hzero t
      simpa only [WR,Pi.zero_apply,Complex.zero_re] using hh
    · simpa using hWreal t
  have hWRb (t : ℝ) : 0≤WR t ∧ WR t≤A :=
    ⟨hWpos t,(Complex.re_le_norm (W t)).trans (hWB t)⟩
  have hcast (t : ℝ) : ((W t).re:ℂ)=W t := by
    apply Complex.ext
    · simp
    · simpa using (hWreal t).symm
  intro eta hk
  have hetacap : eta.k.natAbs≤angularOrder := by simp [hk]
  have hetanonzero : eta.k≠0 := by
    rw [hk]
    exact neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt horder))
  have hbetal := PhysicalZeroSupremum.beta_le_one angularOrder
  obtain ⟨Cp,hCp,hprincipal⟩ := PhysicalPrincipalNormalized.actual_ray_principal_comparison
    M H hH angularOrder eta hetacap hetanonzero S hS 1 2 A ((5/6)*p.rmin)
    (by norm_num) (by norm_num) hA (by positivity) p.ell
    (fun j=>(hslots j).2.1) hellinj hellsum (fun _=>WR) (fun _=>hWR) (fun _=>hWRc)
    (fun _=>hWRs) (fun _=>hWRb) (fun _=>hWRne)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    (principalSignalE p) p.normalizerLoss he hehi p.loss_conditions.2.2.2.1
    (by linarith) (by linarith)
  refine ⟨Cd*(eta.modulus.absNorm:ℝ)^2+2*Cp,by positivity,?_⟩
  filter_upwards [hdet eta hk,hprincipal,eventually_ge_atTop (1:ℝ)] with Z hd hp hZ
  dsimp only at hd hp ⊢
  let Y : Fin p.N→ℝ := fun j=>Z^(p.ell j)
  let T : Fin p.N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T
        (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
  refine ⟨hd.1,?_⟩
  have hpr : ‖principalPhysicalPool eta S T (fun _=>W) Y W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
      PhysicalSignal.signal (eta.excludePrimes S hS.prime)
        (PhysicalPrincipalResidue.sourceCorrection eta S) (-11/16) Z‖≤Cp*
      (Z^(PhysicalZeroSupremum.beta angularOrder-11/16-17/48000+p.normalizerLoss)+
       Z^(PhysicalZeroSupremum.beta angularOrder-11/16+principalSignalE p-(7/8)*((5/6)*p.rmin))) := by
    simpa only [principalPhysicalPool,WR,hcast] using hp.2
  exact actual_normalized_signal_join p (PhysicalZeroSupremum.beta angularOrder) Z
    (Cd*(eta.modulus.absNorm:ℝ)^2) Cp hZ (by positivity) hCp.le _ _ _ normer hd.2 hpr

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_physical_signal_contraction
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_physical_signal_contraction
