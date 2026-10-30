import AngularPhysicalDetectorActualFloorGlobal
import AngularPhysicalDetectorActualCubeNorm
import OAI.NumberTheory.DirichletL.Detector.CentralExponent

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set MeasureTheory
namespace SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowNorm FirstTail dyadicRows mem_dyadicRows smallDyadicIndices mem_smallDyadicIndices bounded_dyadic_power_sum retained_dyadic_sum)
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem globalFloorIntegralPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_global_floor_cube_norm (angularOrder N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀η : AngularCharacter,η.k.natAbs≤angularOrder → ∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀hnp : ∀u∈rows,∀j,(SourceRows.sourceDetectorFamily M H hH S hS.prime η u j).k≠0 ∨ (SourceRows.sourceDetectorFamily M H hH S hS.prime η u j).residue≠1,
      ∀i : ℕ,i≤n →
      (∀u,∀hu : u∈rows,PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M H hH S hS.prime η u) (hnp u hu)
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖commonCubeIntegral S hS hmax η rows T (globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (51/100) e ((3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
            ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  obtain ⟨Ca,hCa,hbound⟩ := actual_global_floor_cube_arithmetic M H hH angularOrder N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_integral_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp*Ca,mul_pos hCp hCa,?_⟩
  intro η horder
  filter_upwards [hbound η horder,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm hnp i hi hbin
  dsimp only
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Yp : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)
  have hp := hprofile e (51/100) ((3*i+1:ℕ)*Z^τ) he he1 le_rfl (by norm_num)
    S hS hmax η rows T (globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp mass
    (by dsimp [mass];positivity) (hb d hd hd' v hv rows hrows hnorm hnp i hi hbin)
  apply hp.2.trans_eq
  rw [physical_central_mellin_scale Z (51/100) e hZp]
  have hpowers : Z^((25/48)*(51/100)-181/300+(105/8)*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)=
      Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
        ProbeCentralExponent.realLoss N v e eps loss mesh) := by
    rw [←Real.rpow_add hZp]
    congr 1
    unfold ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
    ring
  dsimp [mass]
  calc
    _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^((25/48)*(51/100)-181/300+(105/8)*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)) := by ring
    _ = _ := by rw [hpowers]

end SevenEighths.Angular.PhysicalDetectorHigh

end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_global_floor_cube_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_global_floor_cube_norm
