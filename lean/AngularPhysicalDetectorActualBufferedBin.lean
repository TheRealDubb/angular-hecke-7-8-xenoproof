import AngularPhysicalDetectorActualBufferedContour
import AngularPhysicalDetectorLiteralSourceGates

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail
  selectedFirstBound selectedFirstBound_nonneg 
   rowNorm)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)
variable (angularOrder : ℕ)

lemma source_bin_denominator_nonzero (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow)
    (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS η u j).k≠0 ∨ (SourceRows.sourceDetectorFamily M Hray hHray S hS η u j).residue≠1)
    (T a e : ℝ) (i : ℕ) (he : 0<e)
    (hmax : PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS η u) hnp (3*(i+1:ℕ)*T)<a+2*e)
    (x : ℂ) (hx : a+16*e≤x.re) (ht : |x.im|≤3*(i+1:ℕ)*T) :
    FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S hS) x≠0 := by
  have hl := (PhysicalDetectorZeros.zeroMaximum_bounds (SourceRows.sourceDetectorFamily M Hray hHray S hS η u) hnp (3*(i+1:ℕ)*T)).1
  intro hz
  have hb := PhysicalDetectorZeros.zero_re_le_maximum (SourceRows.sourceDetectorFamily M Hray hHray S hS η u) hnp
    (3*(i+1:ℕ)*T) (Sum.inl false) (by linarith) ht hz
  linarith

theorem source_buffered_x_rectangle {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmaxS : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : AngularCharacter) (u : FreeRow) (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨ (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1)
    (T a e : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hfirst : FirstTail (4*e) S)
    (hmax : PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*T)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z)
    (w z : ℂ) (hw : w.re=1-a-6*e) (hz : (17/50:ℝ)≤z.re)
    (r H : ℝ) (hr : a+16*e≤r) (hH : 0≤H) (hHT : H≤3*(i+1:ℕ)*T) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmaxS P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -H..H,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+t*I))+
        I*((∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+(-H)*I))-
          (∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+H*I))) := by
  apply buffered_x_rectangle (8*e) (by positivity) S hS
    (by convert hfirst using 1 ; ring) hmaxS P hPS η u W0 W1 X Y Z hZ w z (a+16*e) r H
    (by linarith) (by linarith) (by rw [hw];linarith) hz (by rw [hw];linarith) (by rw [hw];linarith) (hnp (Sum.inl false))
  intro x hx
  have hxr : a+16*e≤x.re := by simpa only [min_eq_left hr] using hx.1.1
  have hxi : |x.im|≤H := by
    apply abs_le.mpr
    simpa only [uIcc_of_le (by linarith : -H≤H),Set.mem_preimage,Set.mem_Icc] using hx.2
  exact source_bin_denominator_nonzero M Hray hHray S hS.prime η u hnp T a e i he hmax x hxr (hxi.trans hHT)


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.source_bin_denominator_nonzero

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.source_buffered_x_rectangle
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.source_buffered_x_rectangle
