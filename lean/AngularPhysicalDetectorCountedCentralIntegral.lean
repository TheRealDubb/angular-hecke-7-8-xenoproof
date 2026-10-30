import AngularPhysicalDetectorCountedCentralBins
import AngularPhysicalDetectorActualCubeNorm

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

theorem actual_counted_central_integrals
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
    (Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (hone : ∀x∈Icc (0:ℝ) 1,Phi x=1)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (alo bhi B : ℝ) (halo : 0<alo) (hab : alo≤bhi) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo alo bhi) (hφB : ∀y,φ y≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃J : ℕ,∀tau heightPower logCost : ℝ,
      0<tau → tau<dmin/2 → 4*tau<dmin*sourceCost →
      2*tau<dmin*phaseCost → tau*(2+4*eps)<loss →
      tau<heightPower → 0<logCost → logCost+heightPower*J≤dmin*countCost →
      ∃C : ℝ,0<C ∧ ∀eta : AngularCharacter,eta.k= -(angularOrder:ℤ) →
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀d v : ℝ,dmin≤d → d≤dmax → 0≤v →
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
        (∀i k : ℕ,k≠0 → ∀cell : Finset rows,cell.Nonempty →
          (∀u∈cell,idx u=i ∧ grid u=k) →
          let a : ℝ := 51/100+e*k
          let Y : Fin N→ℝ := fun j=>Z^(ell j)
          let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
          ∀ζ μ saving : ℝ,0≤ζ → ζ≤3/16 → v≤13/16+ζ → 0≤μ → d-v≤μ →
            159*epsw+epsm+R+7*nu+countCost≤1/32 →
            (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
              (26*e+(N+8)*eps+loss+mesh/6)+saving≤49/440640 →
            Integrable (commonCubeIntegrand S hS hmax eta (cell.image Subtype.val) T
              (countedPoolOutside M H S N Y) (fun _=>W) Y W0 W1
              (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e ((3*i+1:ℕ)*Z^tau)) heightMeasure ∧
            ‖commonCubeIntegral S hS hmax eta (cell.image Subtype.val) T
              (countedPoolOutside M H S N Y) (fun _=>W) Y W0 W1
              (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e ((3*i+1:ℕ)*Z^tau)‖≤
              C*(eta.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving)) := by
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_integral_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨J,hbase⟩ := actual_counted_central_bins M H hH angularOrder N I
    e eps epsw epsm rmin R dmin dmax lower pad phaseE phaseK phaseCost
    sourceK sourceCost mesh nu countCost loss A bPhi
    he he1 heps hew hew1 hewM hem hem1 hr hR hdmin hdRange hdtop hlower hpad
    hphaseE hphaseK hphaseCost hphaseBudget hphaseGap hsourceK hsourceK1 hsourceCost
    hsourceBudget hmesh hnu hcountCost hA hbPhi hI hwidth hcommonMesh
    S hS hfirst hmax hbad hMmask hMt hM72 ell hell hello hellhi hellsum W hWs hW hWB
    Phi hsPhi hpPhi hone φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
  refine ⟨J,?_⟩
  intro tau heightPower logCost htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  obtain ⟨C,hC,hcells⟩ := hbase tau heightPower logCost
    htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  refine ⟨Cp*C,mul_pos hCp hC,?_⟩
  intro eta hk
  filter_upwards [hcells eta hk] with Z hc
  refine ⟨hc.1,?_⟩
  intro d v hd hd' hv rows hrows hnorm family
  obtain ⟨hnp,idx,grid,hwin,hcellBounds⟩ := hc.2 d v hd hd' hv rows hrows hnorm
  refine ⟨hnp,idx,grid,hwin,?_⟩
  intro i k hk0 cell hne hcell
  dsimp only
  intro ζ μ saving hζ hζ1 hv' hμ hdv hcount hfinal
  let a : ℝ := 51/100+e*k
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S 1 2 (Y j)
  let E : ℝ := (25/48)*a-181/300+(105/8)*e
  let mass : ℝ := C*(eta.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving-E)
  have hZp : 0<Z := zero_lt_one.trans hc.1
  have hm : 0≤mass := by dsimp [mass];positivity
  obtain ⟨u0,hu0⟩ := hne
  have ha0' : (51/100:ℝ)≤a := by
    dsimp [a]
    exact le_add_of_nonneg_right (mul_nonneg he.le (Nat.cast_nonneg k))
  have ha1' : a≤1 := by
    have hh := (hwin u0).2.2.2.1
    simpa only [(hcell u0 hu0).2] using hh
  have hb : ∀t : HeightSpace,
      (|t.1.1|≤(3*i+1:ℕ)*Z^tau ∧ |t.2|≤(3*i+1:ℕ)*Z^tau) ∧
        |t.1.2|≤(3*i+1:ℕ)*Z^tau →
      ‖cubeArithmeticSum S hS hmax eta (cell.image Subtype.val) T
        (countedPoolOutside M H S N Y) (fun _=>W) Y a e t‖≤mass := by
    intro t ht
    exact hcellBounds i k hk0 cell ⟨u0,hu0⟩ hcell t ht ζ μ saving hζ hζ1 hv' hμ hdv hcount hfinal
  have hh := hprofile e a ((3*i+1:ℕ)*Z^tau) he he1 ha0' ha1' S hS hmax
    eta (cell.image Subtype.val) T (countedPoolOutside M H S N Y) (fun _=>W) Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp mass hm hb
  refine ⟨hh.1,?_⟩
  have hp : Z^E*Z^(3/16-saving-E)=Z^(3/16-saving) := by
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  calc
    _ ≤ Cp*((Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e))*mass := hh.2
    _ = (Cp*C)*(eta.modulus.absNorm:ℝ)^(2*eps)*(Z^E*Z^(3/16-saving-E)) := by
      rw [physical_central_mellin_scale Z a e hZp]
      dsimp [mass,E]
      ring
    _ = _ := by rw [hp]

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_central_integrals
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_central_integrals
