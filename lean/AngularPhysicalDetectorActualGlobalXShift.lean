import AngularPhysicalDetectorActualGlobalXBoundary

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail)
local notation "O" => ActualEisensteinCubic.O

theorem global_x_integral_eq (angularCap : ℕ) {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (hk : η.k≠0) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hl : (51/100:ℝ)≤l) (hlβ : (PhysicalZeroSupremum.beta angularCap)+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_global_x_gaussian angularCap e (eps/2) he he' S hS hfirst hmax P hPS
    η horder hk u W0 W1 X Y Z hZ w z l r hl hlβ hw hz (by linarith)
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  apply (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hZ x w z (hl.trans hx.1) hw hz (by linarith [hx.1]) ?_ ?_).differentiableWithinAt
  · exact Or.inl (by simpa only [AngularCharacter.excludePrimes_k,SourceRows.targetRow_k] using hk)
  · apply PhysicalZeroSupremum.LFunction_ne_zero_of_beta_lt angularCap
      ((SourceRows.targetRow η u).excludePrimes S hS.prime)
      (by simpa only [AngularCharacter.excludePrimes_k,SourceRows.targetRow_k] using horder)
      (by linarith [hx.1])
    intro hk0 _
    exact False.elim (hk (by simpa only [AngularCharacter.excludePrimes_k,SourceRows.targetRow_k] using hk0))

end SevenEighths.Angular.PhysicalDetectorHigh

end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.global_x_integral_eq
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.global_x_integral_eq
