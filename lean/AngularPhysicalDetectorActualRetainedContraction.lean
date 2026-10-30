import AngularPhysicalDetectorActualCountedFullBand
import AngularPhysicalDetectorActualBandParameters

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (rowNorm FirstTail)
open HeckeFamily ProbePhysical ProbeMellinBoundary ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual full central band with all numerical budgets discharged.
The target conductor may vary after the common constant is fixed; the
eventual threshold may depend on that target. The same counted windows
survive all finite partitions. This is not the full physical-probe bound. -/
theorem actual_conductor_uniform_band_contraction
    (angularOrder : ℕ) (p : ActualRetainedParameters)
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
    ∃tau C : ℝ,0<tau ∧ tau<ceiling ∧ 0<C ∧
      ∀eta : AngularCharacter,eta.k= -(angularOrder:ℤ) →
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        rowNorm u≤Z^(13/16+p.ζ)) →
      let family := fun u : rows=>SourceRows.sourceDetectorFamily M H hH S hS.prime eta u.val
      ∃hnp : ∀u : rows,∀j,(family u j).k≠0 ∨ (family u j).residue≠1,
      ∃idx grid : rows→ℕ,
        (∀u : rows,1 ≤ idx u ∧ idx u≤p.I ∧ grid u≤⌊(49/100:ℝ)/p.e⌋₊ ∧
          let a : ℝ := 51/100+p.e*grid u
          a≤1 ∧ a≤PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^tau) ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^tau)<a+p.e ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*(idx u+1):ℕ)*Z^tau)<a+2*p.e) ∧
        let Y : Fin p.N→ℝ := fun j=>Z^(p.ell j)
        let T : Fin p.N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
        let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
          (Probe.principalScalar Finset.univ Z (1/6)
            (PrincipalSignalComparison.slotMass T
              (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
        normer≠0 ∧
          ‖finiteCentralCubeRows S hS hmax eta rows T (countedPoolOutside M H S p.N Y)
            (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z p.e
            (fun u=>51/100+p.e*extendRowLabel rows grid u)
            (fun u=>(3*extendRowLabel rows idx u+1:ℕ)*Z^tau)/normer‖≤
              C*(eta.modulus.absNorm:ℝ)^(2*p.eps)*Z^(3/16-p.saving) := by
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  rcases p.mesh_conditions with ⟨hem,hem1,hR,hmesh,hnu,hcountCost,hcommonMesh⟩
  rcases p.slot_conditions with ⟨_hN,_heven,hrmin,hell,hellsum,hslots⟩
  rcases p.early_conditions with ⟨hew,hew1,hewM,_hewr,he,he1,_her,hphaseE,hphaseK,
    hphaseBudget,hphaseGap,hsourceK,hsourceK1,hsourceCost,hsourceBudget⟩
  rcases p.window_conditions with ⟨hI,hwidth⟩
  rcases p.epsilon_conditions with ⟨heps,_hepsr⟩
  rcases p.loss_conditions with ⟨hζ,hμ,hpad,hnLoss,hDL,hsaving,_hloss,hphaseCost⟩
  rcases p.geometry_conditions with ⟨hζμ,hpadTop,hpadMu⟩
  obtain ⟨J,hbase⟩ := actual_counted_full_band M H hH angularOrder p.N p.I
    p.e p.eps p.epsw p.epsm p.rmin p.R (1/200) (5/6) p.pad p.phaseE p.phaseK p.phaseCost
    p.sourceK p.sourceCost p.mesh p.nu p.countCost p.loss A bPhi
    he he1 heps hew hew1 hewM hem hem1 hrmin hR
    (by norm_num) (by norm_num) le_rfl (by norm_num) hpad
    hphaseE hphaseK hphaseCost hphaseBudget hphaseGap hsourceK hsourceK1 hsourceCost
    hsourceBudget hmesh hnu hcountCost.le hA hbPhi hI hwidth hcommonMesh
    S hS hfirst hmax hbad hMmask hMt hM72 p.ell hell (fun j=>(hslots j).2.1)
    (fun j=>(hslots j).2.2) hellsum W hWs hW hWB hWreal hWpos hWne
    Phi hsPhi hpPhi hone φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    p.normalizerLoss hnLoss p.dyadLoss hDL p.ζ p.μ p.saving hζ.le hμ.le hζμ hsaving
    hpadTop hpadMu p.count_budget p.central_budget p.floor_budget
  obtain ⟨heightPower,logCost,tau,_hh0,hlog,htau,hcount,hh,htauzero,htauSource,htauPhase,htauLoss,htceil⟩ :=
    p.late_height ceiling hceiling J
  obtain ⟨C,hC,hresult⟩ := hbase tau heightPower logCost
    htau htauzero htauSource htauPhase htauLoss hh hlog hcount
  exact ⟨tau,C,htau,htceil,hC,hresult⟩

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_conductor_uniform_band_contraction
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_conductor_uniform_band_contraction
