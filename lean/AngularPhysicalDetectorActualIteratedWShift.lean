import AngularPhysicalDetectorActualWShift
import AngularPhysicalDetectorActualKernelInitial

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CubicEisenstein ProbePhysical ProbeMellinBoundary
open HeckeFamily HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

open Filter
open scoped Topology
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions
  marked_firstTail FirstTail selectedFirstBound selectedFirstBound_nonneg
  calibrated_row_nonprincipal calibrated_numerator_first_growth)

local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def shiftedRowInner {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z l : ℝ) (q : ℝ×ℝ) : ℂ :=
  ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((3:ℂ)+q.1*I) ((l:ℂ)+t*I) ((2:ℂ)+q.2*I)

theorem rowIntegral_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (heps' : eps≤5/2)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (l : ℝ) (hl : (1/2:ℝ)≤l) (hl3 : l≤3) :
    Integrable (shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l) (volume.prod volume) ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q ∂(volume.prod volume) := by
  let p : Fin K→O := fun i=>CompletedGauss.primaryGenerator (P i).val
  have hp : ∀i,p i≠0 := fun i=>(supported_primeGenerator_prime (P i)
    (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun v : NonzeroFrequency=>v.val) h)
  have hF := compensatedRows_counting_product_integrable e he η S (calibrationForSet S hmax) p hp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hi : Integrable (compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u))
      heightMeasure := (Measure.ae_count_iff.mp hF.prod_right_ae) u
  have heq (q : ℝ×ℝ) :
      (∫t : ℝ,compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u) (q,t))=
        shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q := by
    have hs := nonprincipal_first_w_integral_eq eps heps S hS hfirst hmax P hPS η u hu W0 W1
      a1 b1 ha1 hW1 X Y Z hY ((3:ℂ)+q.1*I) ((2:ℂ)+q.2*I) l 3 hl3 (by norm_num) (by linarith)
      (by norm_num) (by norm_num;linarith)
    unfold shiftedRowInner
    rw [hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>(continuedPhysicalRowKernel_initial S hS hmax P hP hPS
      η u W0 W1 X Y Z (q,t)).symm)
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall heq)
  · unfold rowIntegral
    rw [integral_prod _ hi]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall heq)


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowIntegral_w_shift
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.rowIntegral_w_shift
