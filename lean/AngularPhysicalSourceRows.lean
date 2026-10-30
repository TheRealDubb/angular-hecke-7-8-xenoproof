import AngularPhysicalCoefficientTransfer
import AngularPrimeDeletion
import OAI.NumberTheory.DirichletL.PrimeRows.Moments

noncomputable section
open scoped Classical ComplexConjugate BigOperators
open Complex
namespace OAI.SevenEighths.Angular.SourceRows
open InverseRows CanonicalRowCompletion
open HeckeInverseAmplification (FreeRow)
open SmoothMobiusCorrection (PrimeIdeal)
open ProbeHighRowFamily (rowMaskElement rowMaskElement_ne_zero momentElement
  rawRow rowCharacter outside_good_coprime rawRow_prime_outside hom_eq_of_primes)
open ProbePhysical (fixedSourcePrincipal prime_coprime_fixedProduct)
local notation "O" => HeckeFamily.O

def momentData (η : AngularCharacter) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

theorem momentData_k (η : AngularCharacter) : (momentData η).η.k=η.k := rfl

theorem momentData_coeff (η : AngularCharacter) (u : FreeRow) (I : Ideal O) :
    ((momentData η).character (momentElement u)).idealHom I=
      η.idealHom I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    (momentData η).character_ideal (momentElement u) I

theorem finite_moment_character_coeff (η : HeckeFamily.Character) (u : FreeRow) (I : Ideal O) :
    ((momentData (AngularCharacter.ofFinite η)).character (momentElement u)).idealHom I=
      HeckeFamily.idealCoeff ((ProbeHighRowFamily.momentData η).character (momentElement u)) I := by
  rw [momentData_coeff,ProbeHighRowFamily.momentData_coeff]
  exact congrArg (fun f : Ideal O→*₀ℂ => f I*idealRowHom (rowMaskElement^6*u.val) I)
    (AngularCharacter.ofFinite_idealHom η)

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter) (u : FreeRow)
    (P : PrimeIdeal) (hP : P.val∉S) :
    ((momentData η).character (momentElement u)).idealHom P.val=
      η.idealHom P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,ite_eq_left hc,one_mul]

theorem excluded_prime (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    (η.excludePrimes S hS).idealHom P.val=if P.val∈S then 0 else η.idealHom P.val := by
  rw [AngularCharacter.idealHom_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

def targetRow (η : AngularCharacter) (u : FreeRow) : AngularCharacter :=
  η.product (AngularCharacter.ofFinite (rawRow u)).conjugate

theorem targetRow_k (η : AngularCharacter) (u : FreeRow) : (targetRow η u).k=η.k := by
  simp [targetRow]

theorem target_inverseRow_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (u : FreeRow) (P : PrimeIdeal) :
    ((targetRow η u).excludePrimes S hS).idealHom P.val=
      if P.val∈S then 0 else η.idealHom P.val*conj (idealRowHom u.val P.val) := by
  rw [excluded_prime]
  by_cases hP : P.val∈S
  · simp only [hP,ite_true]
  · simp only [hP,ite_false,targetRow,AngularCharacter.product_idealHom,
      AngularCharacter.conjugate_idealHom,AngularCharacter.ofFinite_idealHom]
    change η.idealHom P.val*conj (HeckeFamily.idealCoeff (rawRow u) P.val)=_
    rw [rawRow_prime_outside S hS hbad u P hP]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    (AngularCharacter.ofFinite (rowCharacter S hS u)).idealHom I=
      ((momentData (AngularCharacter.ofFinite (fixedSourcePrincipal S hS))).character
        (momentElement u)).idealHom I := by
  rw [AngularCharacter.ofFinite_idealHom,finite_moment_character_coeff]
  exact ProbeHighRowFamily.numerator_moment_coeff S hS hbad u I

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (u : FreeRow) (I : Ideal O) :
    ((targetRow η u).excludePrimes S hS).idealHom I=
      conj (((momentData (η.conjugate.excludePrimes S hS)).character (momentElement u)).idealHom I) := by
  have he : ((targetRow η u).excludePrimes S hS).idealHom=
      ((momentData (η.conjugate.excludePrimes S hS)).character (momentElement u)).conjugate.idealHom := by
    apply hom_eq_of_primes
    intro P
    rw [AngularCharacter.conjugate_idealHom,target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,excluded_prime,ite_eq_left hP,zero_mul,star_zero]
    · rw [ite_eq_right hP,momentData_prime_outside S hS hbad _ u P hP,
        excluded_prime,ite_eq_right hP,AngularCharacter.conjugate_idealHom]
      simp only [star_mul',star_def,starRingEnd_self_apply]
  simpa only [AngularCharacter.conjugate_idealHom,star_def] using
    congrArg (fun f : Ideal O→*₀ℂ => f I) he

#print axioms targetRow_k
#print axioms denominator_moment_coeff
end OAI.SevenEighths.Angular.SourceRows
