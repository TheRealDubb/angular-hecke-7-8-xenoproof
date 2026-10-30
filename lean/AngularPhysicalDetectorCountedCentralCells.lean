import AngularPhysicalDetectorCountedCommonBins
import AngularPhysicalDetectorCentralClassArithmetic
import AngularPhysicalDetectorSlotSupply

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (rowNorm FirstTail)
open HeckeFamily ProbePhysical ProbeMellinBoundary ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
lemma countedPoolOutside (S : Finset (Ideal O)) (N : ℕ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S 1 2 (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S 1 2 (Y j) P).mp hP |>.2.2.2

/-- Actual common-window cell counts supply the cardinality in the literal
central arithmetic sum. No row-count, moment, witness or finite-family Batch
premise is assumed. Geometric, profile and real parameter restrictions stay
explicit. This theorem has not yet identified the sum with a contour. -/
theorem actual_counted_central_cells
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
    (hφs : Function.support φ⊆Ioo alo bhi) (hφB : ∀y,φ y≤B) :
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
          ∀t : HeightSpace,
            ((|t.1.1|≤(3*i+1:ℕ)*Z^tau ∧ |t.2|≤(3*i+1:ℕ)*Z^tau) ∧
              |t.1.2|≤(3*i+1:ℕ)*Z^tau) →
          ∀g : Fin N→ℝ,
            (∀u∈cell,∀j,HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
              (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 (Y j)
                ((17/50:ℂ)+t.1.2*Complex.I))=g j) →
          let q := weightedMean Finset.univ (fun j=>ell j/d) g
          0≤q ∧ q≤(2*a-1)/2 ∧
          ‖cubeArithmeticSum S hS hmax eta (cell.image Subtype.val) T
              (countedPoolOutside M H S N Y) (fun _=>W) Y a e t‖≤
            C*(eta.modulus.absNorm:ℝ)^(2*eps)*
              Z^(d*actualAdaptiveRowExponent (2*a-1) q epsw epsm R nu countCost+
                v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) ∧
          (∀ζ μ saving : ℝ,0≤ζ → ζ≤3/16 → v≤13/16+ζ → 0≤μ → d-v≤μ →
            159*epsw+epsm+R+7*nu+countCost≤1/32 →
            (13/16)*(159*epsw+epsm+R+7*nu+countCost)+2*ζ+(3/2)*μ+
              (26*e+(N+8)*eps+loss+mesh/6)+saving≤49/440640 →
            ‖cubeArithmeticSum S hS hmax eta (cell.image Subtype.val) T
                (countedPoolOutside M H S N Y) (fun _=>W) Y a e t‖≤
              C*(eta.modulus.absNorm:ℝ)^(2*eps)*
                Z^(3/16-saving-((25/48)*a-181/300+(105/8)*e)))) := by
  have hdmax : 0<dmax := hdmin.trans_le hdRange
  obtain ⟨J,hcounts⟩ := PhysicalDetectorLiteralSource.actual_literal_common_bins_counted
    (Slot:=Fin N) M H hH angularOrder W 0 1 bPhi epsm rmin
    (hWs.trans Ioo_subset_Icc_self) hW hbPhi hem hem1 hr Phi hsPhi hpPhi hone
    φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
  refine ⟨J,?_⟩
  intro tau heightPower logCost htau htauzero htauSource htauPhase htauLoss hh hlog hcountBudget
  obtain ⟨C,hC,harith⟩ := actual_class_cube_arithmetic M H hH angularOrder N I
    e eps 1 2 A R dmin dmax rmin tau phaseE phaseK phaseCost mesh lower pad loss
    he he1 heps (by norm_num) (by norm_num) hA hR.le hdmin hdmax.le hdRange hr
    htau hphaseE hphaseK hphaseCost.le hmesh hlower hphaseBudget hphaseGap hpad
    htauPhase htauLoss S hS hfirst hmax ell hell hello hellhi
    (fun _=>W) (fun _=>hWs) (fun _=>hW) (fun _=>hWB) hellsum
  refine ⟨C,hC,?_⟩
  intro eta hk
  have horder : eta.k.natAbs≤angularOrder := by simp [hk]
  have hw := hcounts eta hk S hS.prime hbad hMmask hMt hM72
    dmin dmax tau epsw e sourceK sourceCost lower pad heightPower logCost countCost I
    hdmin hdRange htau htauzero htauSource hew hew1 hewM he he1 hsourceK hsourceK1
    hsourceCost.le hsourceBudget hI hwidth hlower hpad hh hlog hcountCost hcountBudget
  have hf := source_count_frequency_eventually (I+1) dmax tau heightPower hdmax htau hh
  filter_upwards [hw,harith eta horder,hf] with Z hw ha hf
  refine ⟨hw.1,?_⟩
  intro d v hd hd' hv rows hrows hnorm family
  obtain ⟨hQ,hnp,idx,grid,hwin,hcount⟩ := hw.2 d hd hd' rows
    (fun u hu=>(hrows u hu).2.1) (fun u hu=>(hrows u hu).2.2.2)
  refine ⟨hnp,idx,grid,hwin,?_⟩
  intro i k hk0 cell hne hcell
  dsimp only
  intro t ht g hg
  have hZp : 0<Z := zero_lt_one.trans hw.1
  have hd0 : 0<d := hdmin.trans_le hd
  let a : ℝ := 51/100+e*k
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let q : ℝ := weightedMean Finset.univ (fun j=>ell j/d) g
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  obtain ⟨u0,hu0⟩ := hne
  have hi : i≤I := by rw [←(hcell u0 hu0).1];exact (hwin u0).2.1
  have ha0 : 51/100<a := by
    have hkpos : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    dsimp [a];nlinarith
  have ha1 : a≤1 := by
    have hh := (hwin u0).2.2.2.1
    simpa only [(hcell u0 hu0).2] using hh
  have hwidth (j : Fin N) : rmin≤ell j/d ∧ ell j/d≤R := by
    constructor
    · apply (le_div_iff₀ hd0).mpr
      exact (by nlinarith : rmin*d≤dmax*rmin).trans (hello j)
    · apply (div_le_iff₀ hd0).mpr
      exact (hellhi j).trans (by nlinarith)
  have hsupply : 7/37≤∑j : Fin N,ell j/d := by
    rw [←Finset.sum_div,hellsum]
    apply (le_div_iff₀ hd0).mpr
    linarith [hd'.trans hdtop]
  have hheight : |t.1.2|≤Z^heightPower := by
    have hfreq := hf d hd' (I+1) le_rfl
    have hscale : (3*i+1:ℝ)≤3*(I+1:ℕ) := by exact_mod_cast (show 3*i+1≤3*(I+1) by omega)
    have hpi : 0≤2*Real.pi*(Z^d)^(tau/(2*dmax)) := by positivity
    apply ht.2.trans
    have hmul := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hZp.le tau)
    push_cast at hmul hfreq ⊢
    linarith
  have hcap : (2*a-1)/2=a-1/2 := by ring
  have hg' (u : rows) (hu : u∈cell) (j : Fin N) (_hj : j∈(Finset.univ : Finset (Fin N))) :
      HeckePrimeAmplitudeBins.amplitude ((Z^d)^(ell j/d)) ((2*(51/100+e*k)-1)/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 ((Z^d)^(ell j/d)) z)=g j := by
    rw [PhysicalSlotSupply.physical_scale Z d (ell j) hZp hd0.ne']
    change HeckePrimeAmplitudeBins.amplitude (Y j) ((2*a-1)/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 (Y j) z)=g j
    rw [hcap]
    exact hg u hu j
  have hc := hcount i k hk0 cell hcell Finset.univ (fun j=>ell j/d) g (fun _=>z) R mesh nu
    (fun j _=>(hwidth j).1) (fun j _=>(hwidth j).2) hcommonMesh hR.le
    (fun j _=>by norm_num [z]) (fun j _=>by norm_num [z])
    (fun j _=>by simpa [z] using hheight) hmesh hsupply hnu hg'
  let selected : Finset FreeRow := cell.image Subtype.val
  have hsub : selected⊆rows := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact v.property
  have hcard : (selected.card:ℝ)≤1*(Z^d)^(actualAdaptiveRowExponent (2*a-1) q epsw epsm R nu countCost) := by
    have hc' : selected.card=cell.card := Finset.card_image_of_injective _ Subtype.val_injective
    rw [hc',one_mul]
    exact hc
  have hnext (u : FreeRow) (hu : u∈selected) :
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M H hH S hS.prime eta u)
        (hnp ⟨u,hsub hu⟩) (3*(i+1:ℕ)*Z^tau)<a+2*e := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    have hh := (hwin v).2.2.2.2.2.2
    simpa only [a,(hcell v hv).1,(hcell v hv).2,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hmean (u : FreeRow) (hu : u∈selected) :
      weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (Y j) z))=q := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    have heq : (fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H v.val.val W 2 (Y j) z))=g :=
        funext (fun j=>hg v hv j)
    rw [heq]
  have hdelta : 0≤2*a-1 := by linarith
  have hgcap (j : Fin N) (_hj : j∈(Finset.univ : Finset (Fin N))) :
      0≤g j ∧ g j≤(2*a-1)/2 := by
    rw [←hg u0 hu0 j]
    simpa only [hcap] using HeckePrimeAmplitudeBins.amplitude_bounds (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u0.val.val W 2 (Y j) z) (by linarith)
  have hq := weightedMean_bounds Finset.univ (fun j=>ell j/d) g (2*a-1)
    (fun j _=>hr.le.trans (hwidth j).1) (by linarith) hgcap
  have hb := ha d hd hd' v a q 1 (actualAdaptiveRowExponent (2*a-1) q epsw epsm R nu countCost)
    hv ha0.le ha1 (by norm_num) selected (fun u hu=>hrows u (hsub hu))
    (fun u hu=>hnorm u (hsub hu)) hcard (fun u hu=>hnp ⟨u,hsub hu⟩)
    i hi hnext t ht hmean
  simp only [mul_one] at hb
  refine ⟨hq.1,hq.2,hb,?_⟩
  intro ζ μ saving hζ hζ1 hv' hμ hdv hcountBudget hfinalBudget
  have hs := actual_adaptive_mixed_saving N a q epsw epsm R nu countCost
    ζ μ v d e eps loss mesh 0 saving (by linarith) ha1 hq.1 hq.2
    hew.le hem.le hR.le hnu.le hcountCost hcountBudget hζ hζ1 hv' hμ hdv he.le heps.le
    (by simpa only [add_zero] using hfinalBudget)
  have hid := central_class_exponent_identity N a v d
    (actualAdaptiveRowExponent (2*a-1) q epsw epsm R nu countCost) q e eps loss mesh 0
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hw.1.le
  dsimp only [a] at hs hid ⊢
  linarith only [hs,hid]

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.countedPoolOutside

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_central_cells
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_counted_central_cells
