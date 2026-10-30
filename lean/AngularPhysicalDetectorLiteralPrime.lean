import AngularPhysicalDetectorLiteralSource
import AngularPhysicalDetectorAnchorShift
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows PlainRows CommonMask RelativePrime
open OAI.SevenEighths.Angular.Dyadic
open CanonicalRowCompletion CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot (primePool sqrt_inverse_cpow)
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (momentElement)
local notation "O" => ActualEisensteinCubic.O

attribute [local irreducible] AngularCharacter.idealHom naturalRow

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The exact canonical prime amplitude, including its complex conjugation
and all conductor zeros, is a relative angular slot. This is a coefficient
identity, not an assumed energy estimate. -/
theorem canonical_amplitude_relative_slot (eta : AngularCharacter) (u : FreeRow)
    (hMmask : M≤Ideal.span {fixedBadMask})
    (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0<D)
    (hcop : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P eta.modulus) :
    naturalSlot (naturalCharacter eta u.val) (primePool M H b D)
      (fun I=>(rayRelativeCharacter M H hH eta 1).idealHom I *
        HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) I) D =
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b D z) := by
  unfold naturalSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H fixedBadMask
    (dvd_mul_right _ _) hMmask P hclass
  have hcM := HeckePrimeRow.identityClass_coprime M H hclass
  have hcMask := HeckePrimeRow.identityClass_coprime_larger M H hclass hMmask
  have hray : RayQuotient.idealCharacter M H hH 1 P=1 := by
    rw [RayQuotient.idealCharacter_one]
    have hpbot : P≠⊥ := hp.ne_zero
    simp only [hpbot,ite_false,hcM,ite_true]
  have hn : 0<(P.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero)
  have hweight : HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D
      (1-z.re) (-z.im) P = conj (W ((P.absNorm:ℝ)/D)*
        (((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1)) := by
    unfold HeckePrimeAnnular.annularWeight
    rw [map_mul,HeckeInverseAmplification.conj_positive_cpow _ (div_pos hn hD)]
    have he : -HeckeDyadic.shift (1-z.re) (-z.im)=conj (z-1) := by
      apply Complex.ext <;> simp [HeckeDyadic.shift]
    rw [he]
  rw [hweight,naturalCharacter_eq eta u.val u.property.1,NaturalRow.ideal,
    rayRelativeCharacter_coeff,hray,mul_one,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask fixedBadMask P hg,if_pos hcMask,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [hw,zero_mul,mul_zero,map_zero,map_mul,zero_mul,mul_zero]
  · have hc := hcop P hP hw
    have hnorm := PhysicalDetectorJoint.norm_ideal_unit eta P hp.ne_zero hc
    have hcancel : eta.idealHom P*star (eta.idealHom P)=1 := by
      simpa only [Complex.star_def,hnorm,one_pow,Complex.ofReal_one] using
        Complex.mul_conj' (eta.idealHom P)
    simp only [map_mul,starRingEnd_self_apply]
    calc
      _=(eta.idealHom P*star (eta.idealHom P))*
        (idealRowHom u.val P*conj (W ((P.absNorm:ℝ)/D))*
          conj ((((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1))) := by ring
      _=_ := by rw [hcancel,one_mul]

/-- The final detector dictionary is exactly the natural source dictionary
with its original whole-column orientations. In particular the angular
denominator is reversed; the finite numerator is not. -/
theorem literal_source_polynomial (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (eta : AngularCharacter)
    (u : FreeRow) (label : Sum Bool (RayQuotient.Characters M H))
    (inverse : Bool) (W : ℝ→ℂ) (D sigma freq : ℝ) :
    polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
      inverse W D sigma freq =
    polynomial (if ProbeHighRowFamily.sourceMomentReverse M H label then
      (naturalCharacter (SourceRows.sourceMomentData M H hH S hS eta label).η u.val).conjugate
      else naturalCharacter (SourceRows.sourceMomentData M H hH S hS eta label).η u.val)
      inverse W D sigma freq := by
  apply CoefficientTransfer.polynomial_eq_of_idealCoeff
  intro I
  rw [SourceRows.source_family_moment_coeff M H hH S hS hbad]
  have he : ((SourceRows.sourceMomentData M H hH S hS eta label).character
      (momentElement u)).idealHom I =
      (naturalCharacter (SourceRows.sourceMomentData M H hH S hS eta label).η u.val).idealHom I := by
    rcases label with b|theta
    · cases b <;> exact source_moment_natural_coeff _ _ _
    · exact source_moment_natural_coeff _ _ _
  rw [he]
  cases ProbeHighRowFamily.sourceMomentReverse M H label <;>
    simp only [Bool.false_eq_true,ite_false,Bool.true_eq,ite_true,
      AngularCharacter.conjugate_idealHom,Complex.star_def]

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.canonical_amplitude_relative_slot
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.canonical_amplitude_relative_slot

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_polynomial
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_polynomial
