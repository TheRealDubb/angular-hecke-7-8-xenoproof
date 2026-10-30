import AngularPhysicalDetectorLiteralSourceGates
import AngularPhysicalDetectorAdaptiveWitness

/- Buffered zero windows and same-frequency spikes for the literal final
source dictionary. Both nonprincipality and conductor admission are derived
for sufficiently large nonfloor rows. Grid zero is retained as an explicit
floor branch; no spike or contraction is asserted for that branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial PhysicalDetectorJoint
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (rowNorm)
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_literal_source_windows (angularOrder : ℕ)
    (dmin dmax τ eps e κ heightCost lower pad : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (heps : 0<eps) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤eps/2)
    (hI : 0<I) (hwidth : (49/100:ℝ)≤I*e) (hlower : 0<lower) (hpad : 0<pad)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (hη : η.k.natAbs≤angularOrder) (hMt : M≠⊤) (hM72 : M≤Ideal.span {(72:O)}) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀d : ℝ,dmin≤d → d≤dmax →
      ∀rows : Finset FreeRow,(∀u∈rows,Z^lower≤rowNorm u) →
        (∀u∈rows,rowNorm u≤Z^(d-pad)) →
      let family := fun u : rows=>SourceRows.sourceDetectorFamily M H hH S hS η u.val
      (∀u : rows,∀j,initialKeep (SourceRows.sourceMomentData M H hH S hS η j).η
        (internalQ M (SourceRows.sourceMomentData M H hH S hS η j).η) u.val.val) ∧
      (∀u : rows,∀j,((family u j).modulus.absNorm:ℝ)≤Z^d) ∧
      ∃hnp : ∀u : rows,∀j,(family u j).k≠0 ∨ (family u j).residue≠1,
      ∃idx grid : rows → ℕ,
        (∀u : rows,1 ≤ idx u ∧ idx u≤I ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧
          let a : ℝ := 51/100+e*grid u
          a≤1 ∧ a≤PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^τ) ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*idx u:ℕ)*Z^τ)<a+e ∧
          PhysicalDetectorZeros.zeroMaximum (family u) (hnp u) ((3*(idx u+1):ℕ)*Z^τ)<a+2*e ∧
          (∀j t,|t|≤(3*idx u+2:ℕ)*Z^τ → ∀s∈
            Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e),FamilyContinuation.LFunction (family u j) s≠0)) ∧
        (∀u : rows,grid u≠0 → ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (SupportedWitness (family u) (Z^d) (51/100+e*grid u) eps
            tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) (idx u))) := by
  obtain ⟨Z₀,hZ₀⟩ := PhysicalDetectorWitness.supported_from_actual_maximum
    angularOrder dmin dmax τ eps e κ heightCost I
    hdmin hdmax hτ hτzero hτheight heps he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_literal_source_retained M H hH S hS hbad η hMt hM72 lower hlower,
    eventually_literal_source_conductor M H hH S hS η pad hpad,
    eventually_ge_atTop Z₀,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))]
    with Z hret hcond hZ₀' hT
  refine ⟨hret.1,?_⟩
  intro d hd hd' rows hlo hhi family
  have hr (u : rows) := hret.2 u.val (hlo u.val u.property)
  have hQ (u : rows) (j) : ((family u j).modulus.absNorm:ℝ)≤Z^d :=
    hcond.2 u.val d (hhi u.val u.property) j
  let hnp : ∀u : rows,∀j,(family u j).k≠0 ∨ (family u j).residue≠1 := fun u=>(hr u).2
  have hb (u : rows) := PhysicalDetectorZeros.exists_actual_buffered_bin (family u) (hnp u)
    (Z^τ) e hT he I hI hwidth
  choose idx grid hb using hb
  refine ⟨(fun u=>(hr u).1),hQ,hnp,idx,grid,?_,?_⟩
  · intro u
    rcases hb u with ⟨hi1,hiI,ha,hcurrent,hshort,hnext,hatt,hdisc⟩
    have hgrid : grid u≤⌊(49/100:ℝ)/e⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ he).mpr
      linarith only [ha]
    exact ⟨hi1,hiI,hgrid,ha,
      by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcurrent,
      by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hshort,
      by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hnext,hdisc⟩
  · intro u hg tstar ht ht'
    rcases hb u with ⟨hi1,hiI,ha,hcurrent,hshort,hnext,hatt,hdisc⟩
    have hgp : (0:ℝ)<grid u := by exact_mod_cast Nat.pos_of_ne_zero hg
    have ha' : (51/100:ℝ)<51/100+e*grid u := by nlinarith
    have horder (j) : (family u j).k.natAbs≤angularOrder :=
      (literal_source_order M H hH S hS η u.val j).trans hη
    obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hprod,hM,hP⟩ :=
      hZ₀ Z hZ₀' d hd hd' (family u) horder (hnp u) (51/100+e*grid u) (idx u)
        hiI ha' ha hnext (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcurrent)
        (hQ u) tstar ht ht'
    exact ⟨⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
      nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hP⟩,hprod⟩⟩

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.actual_literal_source_windows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.actual_literal_source_windows
