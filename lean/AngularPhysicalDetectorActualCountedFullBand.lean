import AngularPhysicalDetectorActualCountedBand
import AngularPhysicalDetectorActualCubeCalibration
import AngularPhysicalDetectorLiteralSourceWindows

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

theorem actual_counted_full_band
    (angularOrder N I : ℕ)
    (e eps epsw epsm rmin R dmin dmax pad phaseE phaseK phaseCost
      sourceK sourceCost mesh nu countCost loss A bPhi : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hew : 0<epsw) (hew1 : epsw≤1/1000) (hewM : epsw≤epsm/300)
    (hem : 0<epsm) (hem1 : epsm≤1) (hr : 0<rmin) (hR : 0<R)
    (hdmin : 0<dmin) (hdRange : dmin≤dmax) (hdtop : dmax≤5/6)
    (hdmin1 : dmin<1/100) (hpad : 0<pad)
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
    (dyadLoss : ℝ) (hDL : 0<dyadLoss) (ζ μ saving : ℝ) (hζ : 0≤ζ) (hμ : 0≤μ) (hζμ : ζ+μ≤3/16) (hsaving : 0<saving)
    (hpadTop : 13/16+ζ+2*pad≤dmax) (hpadMu : 2*pad≤μ)
    (hcount : 159*epsw+epsm+R+7*nu+countCost≤1/32)
    (hfinal : (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+normalizerLoss+(saving+dyadLoss)≤49/440640)
    (hfloor : 2*(ζ+μ)+26*e+(N+8)*eps+loss+mesh/6+normalizerLoss+(saving+dyadLoss)≤7/1200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃J : ℕ,∀tau heightPower logCost : ℝ,
      0<tau → tau<dmin/2 → 4*tau<dmin*sourceCost →
      2*tau<dmin*phaseCost → tau*(2+4*eps)<loss →
      tau<heightPower → 0<logCost → logCost+heightPower*J≤dmin*countCost →
      ∃C : ℝ,0<C ∧ ∀eta : AngularCharacter,eta.k= -(angularOrder:ℤ) →
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        rowNorm u≤Z^(13/16+ζ)) →
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
  obtain ⟨J,hbase⟩ := actual_counted_retained_band M H hH angularOrder N I
    e eps epsw epsm rmin R dmin dmax pad phaseE phaseK phaseCost
    sourceK sourceCost mesh nu countCost loss A bPhi
    he he1 heps hew hew1 hewM hem hem1 hr hR hdmin hdRange hdtop hdmin1 hpad
    hphaseE hphaseK hphaseCost hphaseBudget hphaseGap hsourceK hsourceK1 hsourceCost
    hsourceBudget hmesh hnu hcountCost hA hbPhi hI hwidth hcommonMesh
    S hS hfirst hmax hbad hMmask hMt hM72 ell hell hello hellhi hellsum W hWs hW hWB
    hWreal hWpos hWne Phi hsPhi hpPhi hone φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 normalizerLoss hnLoss
    dyadLoss hDL ζ μ saving hζ hμ hζμ hsaving hpadTop hpadMu hcount hfinal hfloor
  refine ⟨J,?_⟩
  intro tau heightPower logCost htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  obtain ⟨C,hC,hband⟩ := hbase tau heightPower logCost
    htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  refine ⟨C,hC,?_⟩
  intro eta hk
  have horder : eta.k.natAbs≤angularOrder := by rw [hk];simp
  have hfall := PhysicalDetectorLiteralSource.actual_literal_source_windows M H hH angularOrder
    dmin dmax tau epsw e sourceK sourceCost (1/100) pad I
    hdmin hdRange htau htauzero htauSource hew he he1 hsourceK hsourceK1 hsourceCost.le
    hsourceBudget hI hwidth (by norm_num) hpad S hS.prime hbad eta horder hMt hM72
  filter_upwards [hband eta hk,hfall] with Z hb hf
  refine ⟨hb.1,?_⟩
  intro rows hrows family
  let kept := rows.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0)
  have hkept (u : FreeRow) (hu : u∈kept) :
      u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ) := by
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp hu
    exact ⟨(hrows u hr).1,(hrows u hr).2.1,hc,(hrows u hr).2.2⟩
  obtain ⟨hnpK,ix,gx,hwK,hn,hbK⟩ := hb.2 kept hkept
  have hupper (u : FreeRow) (hu : u∈rows) : rowNorm u≤Z^(dmax-pad) :=
    (hrows u hu).2.2.trans (Real.rpow_le_rpow_of_exponent_le hb.1.le (by linarith))
  obtain ⟨_hkeep,_hQ,hnp0,ix0,gx0,hw0,_hspike⟩ := hf.2 dmax hdRange le_rfl rows
    (fun u hu=>(hrows u hu).2.1) hupper
  let idx : rows→ℕ := fun u=>if hc : (calibrationForSet S hmax).residueMonoid u.val.val≠0
    then ix ⟨u.val,Finset.mem_filter.mpr ⟨u.property,hc⟩⟩ else ix0 u
  let grid : rows→ℕ := fun u=>if hc : (calibrationForSet S hmax).residueMonoid u.val.val≠0
    then gx ⟨u.val,Finset.mem_filter.mpr ⟨u.property,hc⟩⟩ else gx0 u
  refine ⟨hnp0,idx,grid,?_,hn,?_⟩
  · intro u
    by_cases hc : (calibrationForSet S hmax).residueMonoid u.val.val≠0
    · simpa only [idx,grid,dif_pos hc,family] using
        hwK ⟨u.val,Finset.mem_filter.mpr ⟨u.property,hc⟩⟩
    · rcases hw0 u with ⟨h1,h2,h3,h4,h5,h6,h7,_h8⟩
      simpa only [idx,grid,dif_neg hc,family] using
        And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 (And.intro h6 h7)))))
  · have hi (u : FreeRow) (hu : u∈kept) : extendRowLabel rows idx u=extendRowLabel kept ix u := by
      obtain ⟨hr,hc⟩ := Finset.mem_filter.mp hu
      simp only [extendRowLabel,dif_pos hr,dif_pos hu,idx,dif_pos hc]
    have hg (u : FreeRow) (hu : u∈kept) : extendRowLabel rows grid u=extendRowLabel kept gx u := by
      obtain ⟨hr,hc⟩ := Finset.mem_filter.mp hu
      simp only [extendRowLabel,dif_pos hr,dif_pos hu,grid,dif_pos hc]
    let Y : Fin N→ℝ := fun j=>Z^(ell j)
    let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
    have heq : finiteCentralCubeRows S hS hmax eta rows T (countedPoolOutside M H S N Y)
        (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun u=>51/100+e*extendRowLabel rows grid u)
        (fun u=>(3*extendRowLabel rows idx u+1:ℕ)*Z^tau)=
      finiteCentralCubeRows S hS hmax eta kept T (countedPoolOutside M H S N Y)
        (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun u=>51/100+e*extendRowLabel kept gx u)
        (fun u=>(3*extendRowLabel kept ix u+1:ℕ)*Z^tau) := by
      rw [←finiteCentralCubeRows_filter_calibration S hS hmax eta rows T
        (countedPoolOutside M H S N Y) (fun _=>W) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e]
      unfold finiteCentralCubeRows
      apply Finset.sum_congr rfl
      intro u hu
      simp only [hi u hu,hg u hu]
    dsimp only [T,Y] at heq
    dsimp only
    rw [heq]
    exact hbK

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_full_band
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_full_band
