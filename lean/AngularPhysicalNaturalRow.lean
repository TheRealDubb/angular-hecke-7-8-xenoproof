import AngularPhysicalNaturalMask
import AngularPhysicalNonprincipalGate
import AngularPhysicalPlainRowDictionary

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.NaturalRows
open CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource (support_prime coprime_support_iff fixedConductorFactor)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open ExceptionalRows (FixedInducingRow row_mask_mul fixedInducingRow_mul_mask_iff)
local notation "O" => ActualEisensteinCubic.O

structure NaturalRow (η : AngularCharacter) (z : O) where
  character : AngularCharacter
  angular_type : character.k=η.k
  modulus_bound : character.modulus.absNorm≤AngularRowClosure.rowConductorBound η fixedBadMask 1 z
  element : ∀n,character.elementCoeff n=rowTwist (η.elementHom.toMonoidHom) fixedBadMask 1 z n

def naturalRow (η : AngularCharacter) (z : O) (hz : z≠0) : NaturalRow η z := by
  let e := AngularRowClosure.exists_angular_row_character
    η fixedBadMask 1 z fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨Classical.choose e,(Classical.choose_spec e).1,
    (Classical.choose_spec e).2.1,(Classical.choose_spec e).2.2.1⟩

lemma NaturalRow.ideal {η : AngularCharacter} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    F.character.idealHom I=η.idealHom I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using InverseRows.idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : AngularCharacter} {z : O} (F : NaturalRow η z) :
    F.character.elementCoeff 0=0 := by
  rw [F.element]
  change η.elementHom.toMonoidHom 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change η.elementHom.toMonoidHom 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    (excluded F.character R).elementCoeff n=
      rowTwist (η.elementHom.toMonoidHom) (fixedBadMask*idealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (idealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    (excluded F.character R).idealHom I=
      η.idealHom I*idealRowHom ((fixedBadMask*idealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using InverseRows.idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*idealGenerator R) 1 z (F.masked_element R hR) I

lemma NaturalRow.masked_element_span {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (r : O) (hr : r≠0) (n : O) :
    (excluded F.character (Ideal.span {r})).elementCoeff n=
      rowTwist (η.elementHom.toMonoidHom) (fixedBadMask*r) 1 z n := by
  rw [excluded_element F.character (Ideal.span {r})
    (Ideal.span_singleton_eq_bot.not.mpr hr),Ideal.isCoprime_span_singleton_iff,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask r 1 z n (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

theorem NaturalRow.nonprincipal {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (hz : z≠0) (Q R : Ideal O) (hR : R≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    F.character.k≠0 ∨ F.character.residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact ExceptionalRows.actual_row_nonprincipal η F.character F.angular_type Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) hbase

lemma NaturalRow.natural_modulus_bound {η : AngularCharacter} {z : O} (F : NaturalRow η z) :
    F.character.modulus.absNorm≤η.modulus.absNorm*fixedConductorFactor*(Ideal.span {z}).absNorm := by
  have hh:=F.modulus_bound
  simpa [AngularRowClosure.rowConductorBound,fixedConductorFactor,Ideal.span_singleton_one,mul_assoc] using hh

theorem NaturalRow.modulus_power_bound {η : AngularCharacter} {z : O} (F : NaturalRow η z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (_hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m)
    (hz : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (F.character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by
  have hb : (F.character.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(fixedConductorFactor:ℝ)*((Ideal.span {z}).absNorm:ℝ) :=
    by exact_mod_cast F.natural_modulus_bound
  apply hb.trans
  calc
    _≤(Z^m*(fixedConductorFactor:ℝ))*(Cz*Z^q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)) hz
        (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _))
    _=(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by rw [Real.rpow_add hZ]; ring


end OAI.SevenEighths.Angular.NaturalRows

#print axioms OAI.SevenEighths.Angular.NaturalRows.NaturalRow.modulus_power_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.NaturalRow.modulus_power_bound
