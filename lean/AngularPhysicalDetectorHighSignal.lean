import AngularPhysicalDetectorHighProduct
import AngularPhysicalSourceRows
import AngularFamilyContinuation
import OAI.NumberTheory.DirichletL.PrimeRows.Euler

set_option Elab.async false
set_option maxHeartbeats 400000
/- The literal angular source series, including row-ramified primes, factors
with a finite-character numerator and the actual angular denominator.
This theorem is established on the absolute-convergence region only. -/
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic CanonicalRowCompletion
open HeckeInverseAmplification (FreeRow)
open ProbePhysical
open ProbeHighRowFamily (rowCharacter rawRow rowCharacter_hasProd)
open FamilyContinuation (LFunction LFunction_eq_series)
open SourceRows (targetRow target_inverseRow_coeff)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

attribute [local irreducible] FamilyContinuation.LFunction
  AngularCharacter.excludePrimes SourceRows.targetRow

theorem LFunction_hasProd_outside (χ : AngularCharacter) (S : Finset Id) (a : Id→ℂ)
    (ha : ∀P : PrimeIdeal,χ.idealHom P.val=if P.val∈S then 0 else a P.val)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (χ.idealHom) (χ.norm_idealHom_le_one) s hs
  change HasProd _ (χ.series s) at h
  rw [←LFunction_eq_series χ s hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (χ.idealHom) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹ := by
    change (1-χ.idealHom P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹=_
    rw [ha]
    split_ifs <;> simp only [zero_mul,sub_zero,inv_one]
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  by_cases hP : P.val∈S <;> simp only [hP,not_true_eq_false,not_false_eq_true,ite_true,ite_false]

#check LFunction_hasProd_outside

theorem targetRow_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-η.idealHom P.val.val*starRingEnd ℂ (idealRowHom u.val P.val.val)*
        CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction ((targetRow η u).excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (fun P => η.idealHom P*starRingEnd ℂ (idealRowHom u.val P))
    (target_inverseRow_coeff S hS hbad η u) s hs

#check targetRow_hasProd

def localCorrection (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-η.idealHom P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal O)) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

theorem localCorrection_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (markedIdealHighSeries S 1 η u.val x w z *
        (HeckeFamily.LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ * (HeckeFamily.LFunction (rowCharacter S hS u) w)⁻¹ *
          LFunction ((targetRow η u).excludePrimes S hS) x) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hF := excludedIdealHighSeries_row_hasProd_outside S hS η u.val x w z hx hw hz
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz1).inv₀
    (HeckeFamily.LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1)
  have hW := (rowCharacter_hasProd S hS hbad u w hw1).inv₀
    (HeckeFamily.LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1)
  have hD := targetRow_hasProd S hS hbad η u x hx1
  have he := ((hF.mul hZ).mul hW).mul hD
  simpa only [localCorrection,inv_inv,div_eq_mul_inv] using he

#check localCorrection_hasProd

theorem globalCorrection_multipliable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z) :=
  (localCorrection_hasProd S hS hbad η u x w z hx hw hz).multipliable

theorem high_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      HeckeFamily.LFunction (fixedSourcePrincipal S hS) (6*z) * HeckeFamily.LFunction (rowCharacter S hS u) w /
        LFunction ((targetRow η u).excludePrimes S hS) x * globalCorrection S η u x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hZ := HeckeFamily.LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := HeckeFamily.LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := FamilyContinuation.LFunction_ne_zero ((targetRow η u).excludePrimes S hS) x hx1
  rw [globalCorrection,(localCorrection_hasProd S hS hbad η u x w z hx hw hz).tprod_eq]
  field_simp [hZ,hW,hD]


/-- Neither factor changes the source family's angular order. -/
theorem signal_angular_types (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (AngularCharacter.ofFinite (rowCharacter S hS u)).k=0 ∧
      ((targetRow η u).excludePrimes S hS).k=η.k := by
  constructor
  · rfl
  · rw [AngularCharacter.excludePrimes_k,SourceRows.targetRow_k]

end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.targetRow_hasProd

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.high_L_factorization

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.signal_angular_types
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.signal_angular_types
