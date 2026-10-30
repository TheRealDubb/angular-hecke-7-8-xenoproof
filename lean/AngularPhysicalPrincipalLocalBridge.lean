import AngularPhysicalPrincipalProducts
import AngularPhysicalDetectorHighCompensatedContinuation
import AngularPhysicalDetectorActualPrincipalSplit

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalPrincipalProducts
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbePhysical ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "u₁" => PhysicalDetectorHigh.principalFreeRow

lemma principal_not_divisible (P : PrimeIdeal) :
    ¬P.val∣Ideal.span {(u₁).val} := by
  simpa only [PhysicalDetectorHigh.principalFreeRow,Ideal.span_singleton_one,
    ←Ideal.one_eq_top] using P.property.not_dvd_one

lemma principal_continued_marked (η : AngularCharacter) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hz : 1/6<z.re) :
    PhysicalDetectorHigh.continuedMarkedLocal η u₁ P hs x w z=
      idealMarkedClosed η P x w z := by
  have hg := PhysicalDetectorHigh.initial_marked_geometry η P x z hx hz
  rw [PhysicalDetectorHigh.continuedMarkedLocal_unramified η u₁ P hs
    (principal_not_divisible P) x w z hg.1 hg.2]
  change unramifiedMarked _ _ _ (idealRowHom 1 P.val) x w z=_
  rw [idealRowHom_one_supported P.val hs]
  rfl

theorem principal_marked_local_identity (η : AngularCharacter) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    PhysicalDetectorHigh.idealRowMarkedLocalFactor η 1 P x w z=
      idealMarkedClosed η P x w z := by
  exact (PhysicalDetectorHigh.continuedMarkedLocal_eq_initial η u₁ P hs x w z hx hw hz).symm.trans
    (principal_continued_marked η P hs x w z hx hz)

theorem principal_local_correction_identity (η : AngularCharacter) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    PhysicalDetectorHigh.localCorrection η u₁ P x w z=
      PhysicalDetectorHigh.idealClosedCorrection η P x w z := by
  rw [←PhysicalDetectorHigh.finiteLocalCorrection_eq_initial η u₁ P hs x w z hx hw hz]
  unfold PhysicalDetectorHigh.finiteLocalCorrection
  rw [principal_continued_marked η P hs x w z hx hz]
  change continuedCorrection _ (coordW _ (idealRowHom 1 P.val) w)
    (coordD _ _ (idealRowHom 1 P.val) x) _=_
  rw [idealRowHom_one_supported P.val hs]
  rfl

theorem principal_compensated_local_identity (η : AngularCharacter) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    PhysicalDetectorHigh.compensatedLocalCorrection η u₁ P x w z B q=
      compensatedReplacement (coordV P.val.absNorm z) (coordW P.val.absNorm 1 w)
        (coordD P.val.absNorm (η.idealHom P.val) 1 x) (idealMarkedClosed η P x w z) B q := by
  rw [←PhysicalDetectorHigh.continuedCompensatedLocal_eq_initial η u₁ P hs x w z B q hx hw hz]
  unfold PhysicalDetectorHigh.continuedCompensatedLocal
  rw [principal_continued_marked η P hs x w z hx hz]
  change compensatedReplacement _ (coordW _ (idealRowHom 1 P.val) w)
    (coordD _ _ (idealRowHom 1 P.val) x) _ B q=_
  rw [idealRowHom_one_supported P.val hs]

theorem principal_high_local_ne_zero (S : Finset Id) (hS : SourceExclusions S)
    (η : AngularCharacter) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    PhysicalDetectorHigh.idealRowHighLocalFactor η 1 P.val x w z≠0 := by
  have hs := outside_prime_supported S hS.bad P hP
  have hc := correction_ne_zero η S hS.tail P hP x w z (by linarith) (by linarith) (by linarith)
  rw [←principal_local_correction_identity η P hs x w z hx hw hz,
    PhysicalDetectorHigh.localCorrection_eq_normalization] at hc
  exact (mul_ne_zero_iff.mp hc).1

theorem principal_compensated_ratio (S : Finset Id) (hS : SourceExclusions S)
    (η : AngularCharacter) (P : PrimeIdeal) (hP : P.val∉S) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (B*PhysicalDetectorHigh.idealRowMarkedLocalFactor η 1 P x w z-
      q*PhysicalDetectorHigh.idealRowHighLocalFactor η 1 P.val x w z)/
        PhysicalDetectorHigh.idealRowHighLocalFactor η 1 P.val x w z=
      compensatedReplacement (coordV P.val.absNorm z) (coordW P.val.absNorm 1 w)
        (coordD P.val.absNorm (η.idealHom P.val) 1 x) (idealMarkedClosed η P x w z) B q /
          PhysicalDetectorHigh.idealClosedCorrection η P x w z := by
  have hs := outside_prime_supported S hS.bad P hP
  have hc := correction_ne_zero η S hS.tail P hP x w z (by linarith) (by linarith) (by linarith)
  rw [←principal_local_correction_identity η P hs x w z hx hw hz,
    PhysicalDetectorHigh.localCorrection_eq_normalization] at hc
  have hh := (mul_ne_zero_iff.mp hc).1
  have hn := (mul_ne_zero_iff.mp hc).2
  rw [←principal_compensated_local_identity η P hs x w z B q hx hw hz,
    ←principal_local_correction_identity η P hs x w z hx hw hz,
    PhysicalDetectorHigh.compensatedLocalCorrection_eq_raw,
    PhysicalDetectorHigh.localCorrection_eq_normalization]
  exact (mul_div_mul_right _ _ hn).symm

end OAI.SevenEighths.Angular.PhysicalPrincipalProducts

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_not_divisible

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_continued_marked

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_marked_local_identity

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_local_correction_identity

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_compensated_local_identity

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_high_local_ne_zero

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_compensated_ratio
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalProducts.principal_compensated_ratio
