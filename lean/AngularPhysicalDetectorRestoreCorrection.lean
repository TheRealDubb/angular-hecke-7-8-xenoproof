import AngularPhysicalDetectorHighRowBoundary
import AngularPhysicalDetectorHighRowAgreement
import OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Angular.PhysicalDetectorHigh
open ProbeHighRowFamily (unitPart unitPart_coprime multiplicity_lt_six
  markExclusions mem_markExclusions markedSourceExclusions marked_firstTail FirstTail)
open HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def supportedCorrection (η : AngularCharacter) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  if hs : Supported P.val then
    if P.val∣Ideal.span {u.val} then ramifiedCorrection η u P hs x w z
    else idealUnramifiedCorrection η u P x w z
  else 1

def excludedCorrection (S : Finset (Ideal O)) (η : AngularCharacter) (u : FreeRow)
    (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∈S then 1 else supportedCorrection η u P x w z

theorem continuedCorrection_first_hasProd (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    HasProd (fun P : ProbePhysical.PrimeIdeal=>excludedCorrection S η u P x w z)
      (continuedCorrection S hS η u x w z) := by
  have hp := (ramifiedFactor_hasProd S hS η u x w z).mul
    (unramifiedProduct_first_multipliable eps S htail η u x w z hx hz hw hxw).hasProd
  have hsub : HasProd (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S}=>
      excludedCorrection S η u P.val x w z) (continuedCorrection S hS η u x w z) := by
    convert hp using 1
    · funext P
      have hs := outside_prime_supported S hS.bad P.val P.property
      simp only [excludedCorrection,ite_eq_right P.property,supportedCorrection,dite_eq_left hs,
        ramifiedFactor,unramifiedFactor]
      split_ifs <;> simp
    · rfl
  exact (Subtype.val_injective.hasProd_iff (fun P hP=>by
    have hm : P.val∈S := by
      by_contra hn
      exact hP ⟨⟨P,hn⟩,rfl⟩
    simp [excludedCorrection,hm])).mp hsub

theorem continuedCorrection_restore (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    continuedCorrection S hS η u x w z=
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
        ∏P∈T,supportedCorrection η u P x w z := by
  have hlarge := continuedCorrection_first_hasProd eps S hS htail η u x w z hx hz hw hxw
  have hsmall := continuedCorrection_first_hasProd eps (markExclusions S T)
    (markedSourceExclusions S hS T) (marked_firstTail eps S htail T)
    η u x w z hx hz hw hxw
  have hfinite : HasProd (fun P : ProbePhysical.PrimeIdeal=>if P∈T then supportedCorrection η u P x w z else 1)
      (∏P∈T,supportedCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T)
      (f:=fun P : ProbePhysical.PrimeIdeal=>if P∈T then supportedCorrection η u P x w z else 1)
      (L:=SummationFilter.unconditional ProbePhysical.PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hlarge.unique
  convert hsmall.mul hfinite using 1
  funext P
  simp only [excludedCorrection,mem_markExclusions]
  by_cases hp : P∈T
  · simp [hp,hT P hp]
  · simp [hp]

theorem continuedCorrection_restore_quotients (eps : ℝ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (htail : FirstTail eps S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re)
    (G : ProbePhysical.PrimeIdeal→ℂ) (hne : ∀P∈T,supportedCorrection η u P x w z≠0) :
    continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T,G P=continuedCorrection S hS η u x w z*
      ∏P∈T,G P/supportedCorrection η u P x w z := by
  rw [continuedCorrection_restore eps S hS htail T hT η u x w z hx hz hw hxw,
    Finset.prod_div_distrib]
  have hn : (∏P∈T,supportedCorrection η u P x w z)≠0 := Finset.prod_ne_zero_iff.mpr hne
  field_simp
end SevenEighths.Angular.PhysicalDetectorHigh
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_first_hasProd

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_restore

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_restore_quotients
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.continuedCorrection_restore_quotients
