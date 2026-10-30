import AngularPhysicalDetectorActualCountedNormalized
import AngularPhysicalDetectorActualFloorSaving
import AngularPhysicalDetectorActualCommonIntegral
import AngularPhysicalDetectorActualBinPartition

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

theorem actual_counted_dyadic_cube
    (angularOrder N I : ℕ)
    (e eps epsw epsm rmin R dmin dmax lower pad phaseE phaseK phaseCost
      sourceK sourceCost mesh nu countCost loss A bPhi : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hew : 0<epsw) (hew1 : epsw≤1/1000) (hewM : epsw≤epsm/300)
    (hem : 0<epsm) (hem1 : epsm≤1) (hr : 0<rmin) (hR : 0<R)
    (hdmin : 0<dmin) (hdRange : dmin≤dmax) (hdtop : dmax≤5/6)
    (hlower : 0<lower) (hpad : 0<pad)
    (hphaseE : 0<phaseE) (hphaseK : 0<phaseK) (hphaseCost : 0<phaseCost)
    (hphaseBudget : 8*e*R+phaseK≤phaseE) (hphaseGap : phaseE<rmin*mesh)
    (hsourceK : 0<sourceK) (hsourceK1 : sourceK≤1) (hsourceCost : 0<sourceCost)
    (hsourceBudget : 12*e*((22:ℝ)+2)+8*sourceK+2*sourceCost≤epsw/2)
    (hmesh : 0<mesh) (hnu : 0<nu) (hcountCost : 0≤countCost)
    (hA : 0≤A) (hbPhi : 2≤bPhi) (hI : 0<I) (hwidth : (49/100:ℝ)≤I*e)
    (hcommonMesh : R≤PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (hMmask : M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask})
    (hMt : M≠⊤) (hM72 : M≤Ideal.span {(72:O)})
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hellsum : ∑j,ell j=1/6)
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
    (normalizerLoss : ℝ) (hnLoss : 0<normalizerLoss)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hμ : 0≤μ) (hζμ : ζ+μ≤3/16) (hsaving : 0<saving)
    (hcount : 159*epsw+epsm+R+7*nu+countCost≤1/32)
    (hfinal : (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+normalizerLoss+saving≤49/440640)
    (hfloor : 2*(ζ+μ)+26*e+(N+8)*eps+loss+mesh/6+normalizerLoss+saving≤7/1200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃J : ℕ,∀tau heightPower logCost : ℝ,
      0<tau → tau<dmin/2 → 4*tau<dmin*sourceCost →
      2*tau<dmin*phaseCost → tau*(2+4*eps)<loss →
      tau<heightPower → 0<logCost → logCost+heightPower*J≤dmin*countCost →
      ∃C : ℝ,0<C ∧ ∀eta : AngularCharacter,eta.k= -(angularOrder:ℤ) →
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀d v : ℝ,dmin≤d → d≤dmax → 0≤v → v≤13/16+ζ → d-v≤μ →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^lower≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-pad)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      let family := fun u : rows=>SourceRows.sourceDetectorFamily M H hH S hS.prime eta u.val
      ∃hnp : ∀u : rows,∀j,(family u j).k≠0 ∨ (family u j).residue≠1,
      ∃idx grid : rows→ℕ,
        (∀u : rows,1 ≤ idx u ∧ idx u≤I ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧
          let a : ℝ := 51/100+e*grid u
          a≤1 ∧ a≤PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^tau) ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^tau)<a+e ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*(idx u+1):ℕ)*Z^tau)<a+2*e) ∧
        let Y : Fin N→ℝ := fun j=>Z^(ell j)
        let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
        let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
          (Probe.principalScalar Finset.univ Z (1/6)
            (PrincipalSignalComparison.slotMass T
              (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
        normer≠0 ∧
          ‖finiteCentralCubeRows S hS hmax eta rows T (countedPoolOutside M H S N Y)
            (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
            (fun u=>51/100+e*extendRowLabel rows grid u)
            (fun u=>(3*extendRowLabel rows idx u+1:ℕ)*Z^tau)/normer‖≤
              C*(eta.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving) := by
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
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
  have hWRB (y : ℝ) : 0≤WR y ∧ WR y≤A :=
    ⟨hWpos y,(Complex.re_le_norm (W y)).trans (hWB y)⟩
  have hcast (y : ℝ) : (WR y:ℂ)=W y := by
    apply Complex.ext
    · rfl
    · simpa using (hWreal y).symm
  obtain ⟨J,hbase⟩ := actual_counted_normalized_integrals M H hH angularOrder N I
    e eps epsw epsm rmin R dmin dmax lower pad phaseE phaseK phaseCost
    sourceK sourceCost mesh nu countCost loss A bPhi
    he he1 heps hew hew1 hewM hem hem1 hr hR hdmin hdRange hdtop hlower hpad
    hphaseE hphaseK hphaseCost hphaseBudget hphaseGap hsourceK hsourceK1 hsourceCost
    hsourceBudget hmesh hnu hcountCost hA hbPhi hI hwidth hcommonMesh
    S hS hfirst hmax hbad hMmask hMt hM72 ell hell hello hellhi hellsum W hWs hW hWB
    hWreal hWpos hWne Phi hsPhi hpPhi hone φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 normalizerLoss hnLoss
  refine ⟨J,?_⟩
  intro tau heightPower logCost htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  obtain ⟨C,hC,hcells⟩ := hbase tau heightPower logCost
    htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  obtain ⟨Cf,hCf,hfloors⟩ := actual_floor_cube_saving M H hH angularOrder N I
    e eps 1 2 A R dmin dmax rmin tau phaseE phaseK phaseCost mesh lower pad loss
    he he1 heps (by norm_num) (by norm_num) hA hR.le hdmin (hdmin.trans_le hdRange).le hdRange hr
    htau hphaseE hphaseK hphaseCost.le hmesh hlower hphaseBudget hphaseGap hpad htauPhase htauLoss
    S hS hfirst hmax ell hell hello hellhi (fun _=>WR) (fun _=>hWRs) (fun _=>hWR)
    (fun _=>hWRB) (fun _=>hWRc) (fun _=>hWRne) hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 normalizerLoss hnLoss
    (ζ+μ) saving (add_nonneg hζ hμ) hζμ hsaving hfloor
  let m : ℕ := ⌊(49/100:ℝ)/e⌋₊
  refine ⟨(I+1:ℕ)*(m+1:ℕ)*(C+Cf),by positivity,?_⟩
  intro eta hk
  have horder : eta.k.natAbs≤angularOrder := by rw [hk];simp
  filter_upwards [hcells eta hk,hfloors eta horder,source_cube_height_eventually tau htau]
    with Z hc hf hheight
  refine ⟨hc.1,?_⟩
  intro d v hd hd' hv hvhi hdv rows hrows hnorm family
  obtain ⟨hnp,idx,grid,hwin,hcellBounds⟩ := hc.2 d v hd hd' hv rows hrows hnorm
  refine ⟨hnp,idx,grid,hwin,?_⟩
  dsimp only
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T
        (ProbePrincipalResidueActual.residueWeights (fun _=>WR) Y)) : ℂ)
  have hZ0 : 0<Z := zero_lt_one.trans hc.1
  have hd0 : 0<d := hdmin.trans_le hd
  have hdtop' : d≤13/16+(ζ+μ) := by linarith
  have hzero := hf d hd hd' d hd0.le hdtop' ∅ (by simp) (by simp)
    (by simp) 0 (Nat.zero_le _) (by simp)
  have hn : normer≠0 := hzero.1
  refine ⟨hn,?_⟩
  let mass := (C+Cf)*(eta.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving)
  have hmass : 0≤mass := by dsimp [mass];positivity
  have hlabel (u : rows) : idx u≤I ∧ grid u≤m := ⟨(hwin u).2.1,(hwin u).2.2.1⟩
  have hcell : ∀i≤I,∀k≤m,(actualWindowCell rows idx grid i k).Nonempty →
      ‖finiteCentralCubeRows S hS hmax eta
        ((actualWindowCell rows idx grid i k).image Subtype.val) T (countedPoolOutside M H S N Y)
        (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*Z^tau)/normer‖≤mass := by
    intro i hi k hkm hne
    let cell := actualWindowCell rows idx grid i k
    let Rcell : Finset FreeRow := cell.image Subtype.val
    have hlabels (u : rows) (hu : u∈cell) : idx u=i ∧ grid u=k :=
      (Finset.mem_filter.mp hu).2
    have hparent (u : FreeRow) (hu : u∈Rcell) : u∈rows := by
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
      exact w.property
    have hrowsC (u : FreeRow) (hu : u∈Rcell) := hrows u (hparent u hu)
    let hnpC : ∀u∈Rcell,∀j,(SourceRows.sourceDetectorFamily M H hH S hS.prime eta u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M H hH S hS.prime eta u j).residue≠1 :=
      fun u hu=>hnp ⟨u,hparent u hu⟩
    have hbin (u : FreeRow) (hu : u∈Rcell) :
        PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M H hH S hS.prime eta u)
          (hnpC u hu) (3*(i+1:ℕ)*Z^tau)<(51/100+e*k)+2*e := by
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
      have hz := (hwin w).2.2.2.2.2.2
      simpa only [family,(hlabels w hw).1,(hlabels w hw).2,Nat.cast_mul,Nat.cast_ofNat] using hz
    have ha : (51/100:ℝ)≤51/100+e*k := le_add_of_nonneg_right (mul_nonneg he.le (Nat.cast_nonneg k))
    have ha1' : (51/100:ℝ)+e*k≤1 := by
      obtain ⟨u,hu⟩ := hne
      simpa only [(hlabels u hu).2] using (hwin u).2.2.2.1
    have hHeight : (3*i+1:ℕ)*Z^tau≤(3*i+2:ℕ)*Z^tau := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
      exact_mod_cast (by omega : 3*i+1≤3*i+2)
    have hid := cube_common_profile_integral M H hH angularOrder e (51/100+e*k) (Z^tau)
      ((3*i+1:ℕ)*Z^tau) i he he1 ha ha1' hheight.2 hHeight S hS hmax hfirst eta horder Rcell
      (fun u hu=>(hrowsC u hu).1) T (countedPoolOutside M H S N Y) hnpC hbin
      (fun _=>W) Y W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    have heq : finiteCentralCubeRows S hS hmax eta Rcell T (countedPoolOutside M H S N Y)
        (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*Z^tau)=
      commonCubeIntegral S hS hmax eta Rcell T (countedPoolOutside M H S N Y)
        (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (51/100+e*k) e ((3*i+1:ℕ)*Z^tau) := hid.2
    change ‖finiteCentralCubeRows S hS hmax eta Rcell T (countedPoolOutside M H S N Y)
        (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*Z^tau)/normer‖≤mass
    rw [heq]
    by_cases hk0 : k=0
    · subst k
      have hnormC (u : FreeRow) (hu : u∈Rcell) : rowNorm u≤Z^d :=
        (hrowsC u hu).2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith))
      have hb := hf d hd hd' d hd0.le hdtop' Rcell hrowsC hnormC hnpC i hi (by simpa using hbin)
      have hb' : ‖commonCubeIntegral S hS hmax eta Rcell T (countedPoolOutside M H S N Y)
          (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (51/100) e ((3*i+1:ℕ)*Z^tau)/normer‖≤
          Cf*(eta.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving) := by
        simpa only [hcast] using hb.2
      simp only [Nat.cast_zero,mul_zero,add_zero]
      apply hb'.trans
      dsimp [mass]
      gcongr
      linarith
    · have hb := hcellBounds i k hk0 cell hne hlabels ζ μ saving hζ (by linarith) hvhi hμ hdv hcount hfinal
      apply hb.2.2.trans
      dsimp [mass]
      gcongr
      linarith
  have hsum := finiteCentralCubeRows_subtype_bin_norm S hS hmax eta rows T
    (countedPoolOutside M H S N Y) (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
    (Z^tau) idx grid I m hlabel normer mass hmass hcell
  exact hsum.trans_eq (by dsimp [mass];ring)

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_dyadic_cube
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_dyadic_cube
