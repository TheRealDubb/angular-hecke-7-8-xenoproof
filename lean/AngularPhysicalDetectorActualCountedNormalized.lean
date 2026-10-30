import AngularPhysicalDetectorCountedCentralIntegral
import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer

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

theorem actual_counted_normalized_integrals
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
    (normalizerLoss : ℝ) (hnLoss : 0<normalizerLoss) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
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
          let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
            (Probe.principalScalar Finset.univ Z (1/6)
              (PrincipalSignalComparison.slotMass T
                (ProbePrincipalResidueActual.residueWeights (fun _ t=>(W t).re) Y)) : ℂ)
          ∀ζ μ saving : ℝ,0≤ζ → ζ≤3/16 → v≤13/16+ζ → 0≤μ → d-v≤μ →
            159*epsw+epsm+R+7*nu+countCost≤1/32 →
            (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
              (26*e+(N+8)*eps+loss+mesh/6)+normalizerLoss+saving≤49/440640 →
            normer≠0 ∧ Integrable (commonCubeIntegrand S hS hmax eta (cell.image Subtype.val) T
              (countedPoolOutside M H S N Y) (fun _=>W) Y W0 W1
              (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e ((3*i+1:ℕ)*Z^tau)) heightMeasure ∧
            ‖commonCubeIntegral S hS hmax eta (cell.image Subtype.val) T
              (countedPoolOutside M H S N Y) (fun _=>W) Y W0 W1
              (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e ((3*i+1:ℕ)*Z^tau)/normer‖≤
              C*(eta.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving)) := by
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
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hr).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS
    1 2 (by norm_num) (by norm_num) ell hellpos hellsum (fun _=>WR)
    (fun _=>hWR) (fun _=>hWRc) (fun _=>hWRs) (fun _=>hWpos) (fun _=>hWRne)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 normalizerLoss hnLoss
  obtain ⟨J,hbase⟩ := actual_counted_central_integrals M H hH angularOrder N I
    e eps epsw epsm rmin R dmin dmax lower pad phaseE phaseK phaseCost
    sourceK sourceCost mesh nu countCost loss A bPhi
    he he1 heps hew hew1 hewM hem hem1 hr hR hdmin hdRange hdtop hlower hpad
    hphaseE hphaseK hphaseCost hphaseBudget hphaseGap hsourceK hsourceK1 hsourceCost
    hsourceBudget hmesh hnu hcountCost hA hbPhi hI hwidth hcommonMesh
    S hS hfirst hmax hbad hMmask hMt hM72 ell hell hello hellhi hellsum W hWs hW hWB
    Phi hsPhi hpPhi hone φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨J,?_⟩
  intro tau heightPower logCost htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  obtain ⟨C,hC,hcells⟩ := hbase tau heightPower logCost
    htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  refine ⟨C*Cn,mul_pos hC hCn,?_⟩
  intro eta hk
  filter_upwards [hcells eta hk,hnormer] with Z hc hn
  have hZp : 0<Z := zero_lt_one.trans hc.1
  refine ⟨hc.1,?_⟩
  intro d v hd hd' hv rows hrows hnorm family
  obtain ⟨hnp,idx,grid,hwin,hcellBounds⟩ := hc.2 d v hd hd' hv rows hrows hnorm
  refine ⟨hnp,idx,grid,hwin,?_⟩
  intro i k hk0 cell hne hcell
  dsimp only
  intro ζ μ saving hζ hζ1 hv' hμ hdv hcount hfinal
  have hbudget :
      (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
        (26*e+(N+8)*eps+loss+mesh/6)+(saving+normalizerLoss)≤49/440640 := by linarith
  obtain ⟨hInt,hIntBound⟩ := hcellBounds i k hk0 cell hne hcell ζ μ (saving+normalizerLoss)
    hζ hζ1 hv' hμ hdv hcount hbudget
  dsimp only at hn
  refine ⟨hn.1,hInt,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hIntBound hn.2 (norm_nonneg _) (by positivity)).trans_eq
  have hp : Z^(3/16-(saving+normalizerLoss))*Z^normalizerLoss=Z^(3/16-saving) := by
    rw [←Real.rpow_add (zero_lt_one.trans hc.1)]
    congr 1
    ring
  calc
    _ = (C*Cn)*(eta.modulus.absNorm:ℝ)^(2*eps)*
      (Z^(3/16-(saving+normalizerLoss))*Z^normalizerLoss) := by ring
    _ = _ := by rw [hp]

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_normalized_integrals
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_normalized_integrals
