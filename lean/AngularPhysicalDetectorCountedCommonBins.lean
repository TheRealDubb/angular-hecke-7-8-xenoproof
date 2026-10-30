import AngularPhysicalDetectorActualCountExponent
import AngularPhysicalDetectorAbsorbedCommonBins

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

theorem actual_literal_common_bins_counted
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
      ∀dmin dmax tau eps e kappa heightCost lower pad heightPower logCost countCost : ℝ,∀I : ℕ,
        0<dmin → dmin≤dmax → 0<tau → tau<dmin/2 → 4*tau<dmin*heightCost →
        0<eps → eps≤1/1000 → eps≤epsm/300 → 0<e → e<1/1000 →
        0<kappa → kappa≤1 → 0≤heightCost →
        12*e*((22:ℝ)+2)+8*kappa+2*heightCost≤eps/2 →
        0<I → (49/100:ℝ)≤I*e → 0<lower → 0<pad →
        tau<heightPower → 0<logCost → 0≤countCost →
        logCost+heightPower*J≤dmin*countCost →
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
        (∀i k : ℕ,k≠0 →
        ∀cell : Finset rows,(∀u∈cell,idx u=i ∧ grid u=k) →
        ∀(slots : Finset Slot)(w g : Slot→ℝ)(z : Slot→ℂ),
        ∀mesh binWidth nu : ℝ,
          (∀j∈slots,wmin≤w j) → (∀j∈slots,w j≤mesh) →
          mesh≤PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2) → 0≤mesh →
          (∀j∈slots,lo≤1-(z j).re) → (∀j∈slots,1-(z j).re≤hi) →
          (∀j∈slots,|(z j).im|≤Z^heightPower) →
          0<binWidth → 7/37≤∑j∈slots,w j → 0<nu →
          (∀u∈cell,∀j∈slots,HeckePrimeAmplitudeBins.amplitude ((Z^d)^(w j))
            ((2*(51/100+e*k)-1)/2) binWidth
            (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 ((Z^d)^(w j)) (z j))=g j) →
          (cell.card:ℝ)≤(Z^d)^(PhysicalDetectorHigh.actualAdaptiveRowExponent
            (2*(51/100+e*k)-1) (weightedMean slots w g) eps epsm mesh nu countCost)) := by
  obtain ⟨J,hw⟩ := actual_literal_common_bins_absorbed (Slot:=Slot) M H hH n W lo hi bPhi epsm wmin
    hWs hW hbPhi hepsm hepsm1 hwmin Phi hsPhi hpPhi hone
    φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
  refine ⟨J,?_⟩
  intro eta hk S hS hbad hMmask hMt hM72
  intro dmin dmax tau eps e kappa heightCost lower pad heightPower logCost countCost I
    hdmin hdmax htau htauzero htauheight heps heps1 hepad he he1 hkappa hkappa1
    hheightCost hbudget hI hwidth hlower hpad hheightPower hlog hcountCost hcostBudget
  filter_upwards [hw eta hk S hS hbad hMmask hMt hM72
    dmin dmax tau eps e kappa heightCost lower pad heightPower logCost countCost I
    hdmin hdmax htau htauzero htauheight heps heps1 hepad he he1 hkappa hkappa1
    hheightCost hbudget hI hwidth hlower hpad hheightPower hlog hcountCost hcostBudget] with Z hw
  refine ⟨hw.1,?_⟩
  intro d hd hd' rows hrowlo hrowhi family
  obtain ⟨hQ,hnp,idx,grid,hwin,hbalanced,hhigh⟩ := hw.2 d hd hd' rows hrowlo hrowhi
  refine ⟨hQ,hnp,idx,grid,hwin,?_⟩
  intro i k hk0 cell hcell slots w g z mesh binWidth nu
    hwslot hwm hmesh hmesh0 hlo hhi hz hbin hsupply hnu hbins
  by_cases hdelta : 2*(51/100+e*k)-1≤5/6
  · have hc := hbalanced i k hk0 hdelta cell hcell slots w g z mesh binWidth nu
      hwslot hwm hmesh hmesh0 hlo hhi hz hbin hsupply hnu hbins
    simpa only [PhysicalDetectorHigh.actualAdaptiveRowExponent,if_pos hdelta] using hc
  · let full : Finset rows := Finset.univ.filter (fun u=>idx u=i ∧ grid u=k)
    have hsub : cell⊆full := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcell u hu⟩
    have hc : (cell.card:ℝ)≤(full.card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hb := hhigh i k (le_of_lt (lt_of_not_ge hdelta))
    have result := hc.trans hb
    rw [PhysicalDetectorHigh.actualAdaptiveRowExponent,if_neg hdelta]
    simpa only [add_assoc,add_comm,add_left_comm] using result

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.actual_literal_common_bins_counted
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.actual_literal_common_bins_counted
