import AngularPhysicalDetectorLiteralBalancedWitness
import AngularPhysicalDetectorLiteralSharpHigh
import AngularPhysicalDetectorLiteralSourceWindows

/- Both row-count ranges refer to one actual buffered-window selection.
The degree is fixed before eta and S; the common constant is fixed before
tau and all moving rows. Actual conductor gates are retained for the
finite ray/prime bridge. This theorem does not estimate the contour. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial PhysicalDetectorJoint
open HeckeInverseAmplification (FreeRow)
open HeckeDetectorWitnessRows (dyadicLength)
open HeckeDetectorPhysicalSelection HeckeDetectorRowCount
open ProbeHighRowFamily (rowNorm)
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local notation "Label" => Sum Bool (RayQuotient.Characters M H)

theorem actual_literal_common_bins
    (n : ℕ) (W : ℝ→ℂ) (lo hi bPhi epsm wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbPhi : 2≤bPhi) (hepsm : 0<epsm) (hepsm1 : epsm≤1) (hwmin : 0<wmin)
    (Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (hone : ∀x∈Icc (0:ℝ) 1,Phi x=1)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (alo bhi B : ℝ) (halo : 0<alo) (hab : alo≤bhi) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo alo bhi) (hφB : ∀y,φ y≤B) :
    ∃J : ℕ,∀eta : AngularCharacter,eta.k= -(n:ℤ) →
      ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      CanonicalQuadraticSieve.fixedBadPrimes⊆S →
      M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} →
      M≠⊤ → M≤Ideal.span {(72:O)} →
      ∃C : ℝ,0<C ∧
      ∀dmin dmax tau eps e kappa heightCost lower pad : ℝ,∀I : ℕ,
        0<dmin → dmin≤dmax → 0<tau → tau<dmin/2 → 4*tau<dmin*heightCost →
        0<eps → eps≤1/1000 → eps≤epsm/300 → 0<e → e<1/1000 →
        0<kappa → kappa≤1 → 0≤heightCost →
        12*e*((22:ℝ)+2)+8*kappa+2*heightCost≤eps/2 →
        0<I → (49/100:ℝ)≤I*e → 0<lower → 0<pad →
      ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀d : ℝ,dmin≤d → d≤dmax →
      ∀rows : Finset FreeRow,(∀u∈rows,Z^lower≤rowNorm u) →
        (∀u∈rows,rowNorm u≤Z^(d-pad)) →
      let family := fun u : rows=>SourceRows.sourceDetectorFamily M H hH S hS eta u.val
      (∀u : rows,∀j,((family u j).modulus.absNorm:ℝ)≤Z^d) ∧
      ∃hnp : ∀u : rows,∀j,(family u j).k≠0 ∨ (family u j).residue≠1,
      ∃idx grid : rows→ℕ,
        (∀u : rows,1 ≤ idx u ∧ idx u≤I ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧
          let a : ℝ := 51/100+e*grid u
          a≤1 ∧ a≤PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^tau) ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^tau)<a+e ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*(idx u+1):ℕ)*Z^tau)<a+2*e) ∧
        (∀i k : ℕ,k≠0 → 2*(51/100+e*k)-1≤5/6 →
        ∀cell : Finset rows,(∀u∈cell,idx u=i ∧ grid u=k) →
        ∀(slots : Finset Slot)(w g : Slot→ℝ)(z : Slot→ℂ),
        ∀height mesh binWidth nu : ℝ,
          (∀j∈slots,wmin≤w j) → (∀j∈slots,w j≤mesh) →
          mesh≤PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2) → 0≤mesh →
          (∀j∈slots,lo≤1-(z j).re) → (∀j∈slots,1-(z j).re≤hi) →
          0≤height → (∀j∈slots,|(z j).im|≤height) →
          0<binWidth → 7/37≤∑j∈slots,w j → 0<nu →
          2*Real.pi*(Z^d)^(tau/(2*dmax))+(3*I:ℕ)*Z^tau≤height →
          (∀u∈cell,∀j∈slots,HeckePrimeAmplitudeBins.amplitude ((Z^d)^(w j))
            ((2*(51/100+e*k)-1)/2) binWidth
            (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 ((Z^d)^(w j)) (z j))=g j) →
          (cell.card:ℝ)≤((Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2)*
            (C*(1+height)^J)*(Z^d)^(Endpoint.balancedRowCount (2*(51/100+e*k)-1)
              (1/2-weightedMean slots w g/(2*(51/100+e*k)-1))+159*eps+epsm+mesh+7*nu)) ∧
        (∀i g : ℕ,5/6≤2*(51/100+e*g)-1 →
          (((Finset.univ : Finset rows).filter (fun u=>idx u=i ∧ grid u=g)).card:ℝ)≤
            ((Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2)*
            (C*(1+(2*Real.pi*(Z^d)^(tau/(2*dmax))+(3*I:ℕ)*Z^tau))^J)*
            (Z^d)^((1-(2*(51/100+e*g)-1))+epsm+78*eps)) := by
  obtain ⟨Jb,hbalanced⟩ := literal_balanced_witness_rows (Slot:=Slot) M H hH n W lo hi bPhi epsm wmin
    hWs hW hbPhi hepsm hepsm1 hwmin Phi hsPhi hpPhi hone
    φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
  obtain ⟨Jh,hhigh⟩ := literal_sharp_high_witness_rows M H hH n φ hφ hφc hφp hφ0 hφne
    alo bhi B halo hab hB hφs hφB epsm hepsm
  refine ⟨Jb+Jh,?_⟩
  intro eta hk S hS hbad hMmask hMt hM72
  obtain ⟨Cb,hCb,hbalanced⟩ := hbalanced eta hk S hS hbad hMmask hMt hM72
  obtain ⟨Ch,hCh,hhigh⟩ := hhigh eta hk S hS hbad
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hbalanced
  obtain ⟨V0,hV0⟩ := eventually_atTop.mp hhigh
  have hbalancedScale (height : ℝ) (hh : 0≤height) :
      Cb*(1+height)^Jb≤(Cb+Ch)*(1+height)^(Jb+Jh) := by
    exact mul_le_mul (le_add_of_nonneg_right hCh.le)
      (pow_le_pow_right₀ (by linarith) (Nat.le_add_right Jb Jh))
      (by positivity) (by positivity)
  have hhighScale (height : ℝ) (hh : 0≤height) :
      Ch*(1+height)^Jh≤(Cb+Ch)*(1+height)^(Jb+Jh) := by
    exact mul_le_mul (le_add_of_nonneg_left hCb.le)
      (pow_le_pow_right₀ (by linarith) (Nat.le_add_left Jh Jb))
      (by positivity) (by positivity)
  refine ⟨Cb+Ch,by positivity,?_⟩
  intro dmin dmax tau eps e kappa heightCost lower pad I hdmin hdmax htau htauzero htauheight
    heps heps1 hepad he he1 hkappa hkappa1 hheightCost hbudget hI hwidth hlower hpad
  have heta : eta.k.natAbs≤n := by simp [hk]
  have hlarge : ∀ᶠZ : ℝ in atTop,max U0 V0≤Z^dmin :=
    (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop _)
  filter_upwards [actual_literal_source_windows M H hH n dmin dmax tau eps e kappa heightCost lower pad I
    hdmin hdmax htau htauzero htauheight heps he he1 hkappa hkappa1 hheightCost hbudget hI hwidth
    hlower hpad S hS hbad eta heta hMt hM72,hlarge] with Z hWin hlarge
  refine ⟨hWin.1,?_⟩
  intro d hd hd' rows hrowlo hrowhi family
  obtain ⟨hret,hQ,hnp,idx,grid,hwin,hwitness⟩ := hWin.2 d hd hd' rows hrowlo hrowhi
  have hthreshold := hlarge.trans (Real.rpow_le_rpow_of_exponent_le hWin.1.le hd)
  have hcU := hU0 (Z^d) ((le_max_left U0 V0).trans hthreshold)
  have hhU := hV0 (Z^d) ((le_max_right U0 V0).trans hthreshold)
  refine ⟨hQ,hnp,idx,grid,?_,?_,?_⟩
  · intro u
    rcases hwin u with ⟨hi1,hiI,hg,ha,hcurrent,hshort,hnext,hdisc⟩
    exact ⟨hi1,hiI,hg,ha,hcurrent,hshort,hnext⟩
  · intro i k hk0 hdelta cell hcell slots w g z height mesh binWidth nu
      hw hwm hmesh hmesh0 hlo hhi hh hz hbin hsupply hnu hheight hbins
    have hZp : 0<Z := zero_lt_one.trans hWin.1
    by_cases hne : cell.Nonempty
    · let selected : Finset FreeRow := cell.image Subtype.val
      have hselected : selected⊆rows := by
        intro u hu
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        exact v.property
      let original (u : selected) : rows := ⟨u.val,hselected u.property⟩
      have horiginal (u : selected) : original u∈cell := by
        obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp u.property
        have heq : v=original u := Subtype.ext hvu
        simpa only [heq] using hv
      have fields (u : selected) : idx (original u)=i ∧ grid (original u)=k :=
        hcell _ (horiginal u)
      obtain ⟨v,hv⟩ := hne
      have hiI : i≤I := by rw [←(hcell v hv).1];exact (hwin v).2.1
      have hkp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have ha : (51/100:ℝ)<51/100+e*k := by nlinarith
      let delta := 2*(51/100+e*k)-1
      let x := weightedMean slots w g/delta
      let tstar := Endpoint.balancedCutoff delta (1/2-x)
      have hdp : 0<delta := by dsimp [delta];linarith
      have hL : 0<∑j∈slots,w j := by linarith
      have hg (j : Slot)(hj : j∈slots) : 0≤g j ∧ g j≤delta/2 := by
        rw [←hbins v hv j hj]
        exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by dsimp [delta] at hdp;linarith)
      obtain ⟨hq0,hq1⟩ := weightedMean_bounds slots w g delta
        (fun j hj=>hwmin.le.trans (hw j hj)) hL hg
      have hx : 0≤x := div_nonneg hq0 hdp.le
      have hx1 : x≤1/2 := (div_le_iff₀ hdp).mpr (by linarith)
      have hts := balanced_cutoff_bounds hdp.le hdelta hx hx1
      have witness (u : selected) : SupportedWitness
          (SourceRows.sourceDetectorFamily M H hH S hS eta u.val) (Z^d)
          (51/100+e*k) eps tstar (Z^tau) ((Z^d)^(tau/(2*dmax))) i := by
        have hg0 : grid (original u)≠0 := by rw [(fields u).2];exact hk0
        have ww := Classical.choice (hwitness (original u) hg0 tstar hts.1 hts.2)
        simpa only [(fields u).1,(fields u).2] using ww
      have hfreq : 2*Real.pi*(Z^d)^(tau/(2*dmax))+(3*i:ℕ)*Z^tau≤height := by
        apply le_trans _ hheight
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.mul_le_mul_left 3 hiI) (Real.rpow_nonneg hZp.le _)
      have hnorm : ∀u∈selected,((Ideal.span {u.val}).absNorm:ℝ)≤Z^d := by
        intro u hu
        exact (hrowhi u (hselected hu)).trans
          (Real.rpow_le_rpow_of_exponent_le hWin.1.le (by linarith))
      have hb := hcU.2 slots w g z height mesh binWidth (51/100+e*k) eps nu
        (Z^tau) ((Z^d)^(tau/(2*dmax))) i hw hwm hmesh hmesh0 hlo hhi hh hz hbin hsupply
        ha hdelta heps.le heps1 hepad hnu hfreq selected
        (fun u hu j=>hret ⟨u,hselected hu⟩ j) hnorm
        (by
          intro u hu
          obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
          exact hbins v hv) witness
      have hcard : selected.card=cell.card := Finset.card_image_of_injective _ Subtype.val_injective
      rw [hcard] at hb
      apply hb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbalancedScale height hh) (by positivity))
        (Real.rpow_nonneg (Real.rpow_nonneg hZp.le _) _)
    · have he : cell=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,Finset.card_empty,Nat.cast_zero]
      positivity

  · intro i g hgHigh
    let f : Finset rows := Finset.univ.filter (fun u=>idx u=i ∧ grid u=g)
    let selected : Finset FreeRow := f.image Subtype.val
    let height := 2*Real.pi*(Z^d)^(tau/(2*dmax))+(3*I:ℕ)*Z^tau
    have hZp : 0<Z := zero_lt_one.trans hWin.1
    have hh : 0≤height := by dsimp [height];positivity
    by_cases hne : f.Nonempty
    · have hselected : selected⊆rows := by
        intro u hu
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        exact v.property
      let original (u : selected) : rows := ⟨u.val,hselected u.property⟩
      have horiginal (u : selected) : original u∈f := by
        obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp u.property
        have heq : v=original u := Subtype.ext hvu
        simpa only [heq] using hv
      have fields (u : selected) : idx (original u)=i ∧ grid (original u)=g :=
        (Finset.mem_filter.mp (horiginal u)).2
      have hg0 : g≠0 := by
        intro hg
        norm_num [hg] at hgHigh
      have witness (u : selected) : SupportedWitness
          (SourceRows.sourceDetectorFamily M H hH S hS eta u.val) (Z^d)
          (51/100+e*g) eps (3/2) (Z^tau) ((Z^d)^(tau/(2*dmax))) i := by
        have hg' : grid (original u)≠0 := by rw [(fields u).2];exact hg0
        have w := Classical.choice (hwitness (original u) hg' (3/2) (by norm_num) le_rfl)
        simpa only [(fields u).1,(fields u).2] using w
      obtain ⟨v,hv⟩ := hne
      have hvf := (Finset.mem_filter.mp hv).2
      have hiI : i≤I := by rw [←hvf.1];exact (hwin v).2.1
      have ha : 51/100+e*g≤1 := by rw [←hvf.2];exact (hwin v).2.2.2.1
      have hfreq : 2*Real.pi*(Z^d)^(tau/(2*dmax))+(3*i:ℕ)*Z^tau≤height := by
        dsimp only [height]
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.mul_le_mul_left 3 hiI) (Real.rpow_nonneg hZp.le _)
      have hnorm : ∀u∈selected,((Ideal.span {u.val}).absNorm:ℝ)≤Z^d := by
        intro u hu
        exact (hrowhi u (hselected hu)).trans
          (Real.rpow_le_rpow_of_exponent_le hWin.1.le (by linarith))
      have hb := hhU.2 selected hnorm (51/100+e*g) eps (Z^tau) ((Z^d)^(tau/(2*dmax))) height i
        hgHigh (by linarith) heps.le heps1 hh hfreq witness
      have hcard : selected.card=f.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      rw [hcard] at hb
      apply hb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hhighScale height hh) (by positivity))
        (Real.rpow_nonneg (Real.rpow_nonneg hZp.le _) _)
    · have hf : f=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (f.card:ℝ)≤_
      rw [hf,Finset.card_empty,Nat.cast_zero]
      positivity

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.actual_literal_common_bins
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.actual_literal_common_bins
