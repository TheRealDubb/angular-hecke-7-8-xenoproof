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

/-- At fixed positive angular order, the actual physical probe minus its
principal pool has a strict saving. C precedes the target and its conductor;
the eventual threshold may depend on the target. The principal pool still
requires its separate signal comparison. The counted windows are reused. -/
theorem actual_conductor_uniform_physical_contraction
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
    ∃C : ℝ,0<C ∧ ∀eta : AngularCharacter,eta.k= -(angularOrder:ℤ) →
      ∀ᶠZ : ℝ in atTop,
      let Y : Fin p.N→ℝ := fun j=>Z^(p.ell j)
      let T : Fin p.N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
      normer≠0 ∧
        ‖(PhysicalDetectorProbe.compensatedPhysicalProbe eta (calibrationForSet S hmax) W0 W1
            (fun j=>canonicalSlotSupport (T j)) (fun _=>W) Y (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
          principalPhysicalPool eta S T (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)/normer‖≤
          C*(eta.modulus.absNorm:ℝ)^2*Z^(PhysicalZeroSupremum.beta angularOrder-11/16-p.saving) := by
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨tau,Cc,htau,htceil,hCc,hcentral⟩ := actual_conductor_uniform_band_contraction
    M H hH angularOrder p A bPhi ceiling hA hbPhi hceiling S hS hfirst hmax hbad
    hMmask hMt hM72 W hWs hW hWB hWreal hWpos hWne Phi hsPhi hpPhi hone
    φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  rcases actual_physical_join_budget p with ⟨he,he1,hz,hz1,heps,htail,hunit⟩
  obtain ⟨Ca,hCa,hcanonical⟩ := canonical_probe_minus_cube M H hH angularOrder p.N
    p.e (1/2) 1 2 A p.ζ 1 tau he he1 (by norm_num) le_rfl hz hz1 htau
    (by norm_num) (by norm_num) hA hbeta S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  rcases p.slot_conditions with ⟨hN,heven,hrmin,hellinj,hellsum,hslots⟩
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
  obtain ⟨Cn,hCn,hnormer⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS
    1 2 (by norm_num) (by norm_num) p.ell (fun j=>(hslots j).1) hellsum (fun _=>WR)
    (fun _=>hWR) (fun _=>hWRc) (fun _=>hWRs) (fun _=>hWpos) (fun _=>hWRne)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    p.normalizerLoss p.loss_conditions.2.2.2.1
  refine ⟨Cc+2*Ca*Cn,by positivity,?_⟩
  intro eta hk
  have hetacap : eta.k.natAbs≤angularOrder := by simp [hk]
  have hetanonzero : eta.k≠0 := by
    rw [hk]
    exact neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt horder))
  filter_upwards [hcentral eta hk,hnormer,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin p.N=>(1:ℝ)) (fun _=>(2:ℝ)) p.ell
      (fun _=>by norm_num) (fun _=>by norm_num) hellinj,
    ProbeHighRowFamily.source_cube_height_eventually tau htau] with Z hc hn hd hheight
  have hZ : 1≤Z := hc.1.le
  have hZp : 0<Z := lt_trans zero_lt_one hc.1
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+p.ζ))
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^(13/16+p.ζ) := by
    intro u hu
    exact ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.1,(mem_rowBand.mp hu).2.2.le⟩
  obtain ⟨hnp,idx,grid,hwin,hcc⟩ := hc.2 rows hrows
  let Y : Fin p.N→ℝ := fun j=>Z^(p.ell j)
  let T : Fin p.N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
  let hT := countedPoolOutside M H S p.N Y
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T
        (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
  let alpha : FreeRow→ℝ := fun u=>51/100+p.e*extendRowLabel rows grid u
  let height : FreeRow→ℝ := fun u=>(3*extendRowLabel rows idx u+1:ℕ)*Z^tau
  let base : FreeRow→ℝ := fun _=>Z^tau
  have hnp' : ∀u∈rows,∀j,(SourceRows.sourceDetectorFamily M H hH S hS.prime eta u j).k≠0 ∨
      (SourceRows.sourceDetectorFamily M H hH S hS.prime eta u j).residue≠1 :=
    fun u hu=>hnp ⟨u,hu⟩
  have hpool (j : Fin p.N) (P : PrimeIdeal) (hP : P∈T j) :
      (P.val.absNorm:ℝ)≤2*Z^(p.ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S
      (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2)
      (Real.rpow_pos_of_pos hZp (p.ell j)) P hP).2
    simpa only [mul_comm] using hh
  have hbin (u : FreeRow) (hu : u∈rows) :
      (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^tau≤height u ∧
      height u≤(3*extendRowLabel rows idx u+2:ℕ)*base u ∧
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M H hH S hS.prime eta u)
        (hnp' u hu) (3*(extendRowLabel rows idx u+1:ℕ)*base u)<alpha u+2*p.e := by
    have hw := hwin ⟨u,hu⟩
    have hidx : extendRowLabel rows idx u=idx ⟨u,hu⟩ := by simp [extendRowLabel,hu]
    have hgrid : extendRowLabel rows grid u=grid ⟨u,hu⟩ := by simp [extendRowLabel,hu]
    dsimp only [alpha,height,base]
    rw [hidx,hgrid]
    refine ⟨?_,hw.2.2.2.1,hheight.2,?_,?_,?_⟩
    · have hh : 0≤p.e*(grid ⟨u,hu⟩:ℝ) := mul_nonneg he.le (Nat.cast_nonneg _)
      linarith
    · have hmult : (1:ℝ)≤(3*idx ⟨u,hu⟩+1:ℕ) := by exact_mod_cast (by omega : 1≤3*idx ⟨u,hu⟩+1)
      simpa using mul_le_mul_of_nonneg_right hmult (Real.rpow_nonneg hZp.le tau)
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 3*idx ⟨u,hu⟩+1≤3*idx ⟨u,hu⟩+2))
        (Real.rpow_nonneg hZp.le tau)
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hw.2.2.2.2.2.2
  have herr := hcanonical eta hetacap hetanonzero Z hZ T hT hd p.ell
    (fun j=>(hslots j).1.le) hellsum hpool (fun _=>W)
    (fun _=>hWs.trans Ioo_subset_Icc_self) (fun _=>hWB)
    alpha base height (extendRowLabel rows idx) hnp' hbin
  change normer≠0 ∧ ‖normer⁻¹‖≤Cn*Z^p.normalizerLoss at hn
  refine ⟨hn.1,?_⟩
  exact actual_normalized_physical_join p (PhysicalZeroSupremum.beta angularOrder) Z
    (eta.modulus.absNorm:ℝ) Cc Ca Cn hbeta hZ (PhysicalLogarithmic.modulus_norm_ge_one eta)
    hCc.le hCa.le hCn.le _ _ _ normer hcc.2 herr hn.2

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_conductor_uniform_physical_contraction
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_conductor_uniform_physical_contraction
