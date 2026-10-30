import AngularPhysicalDetectorReflectedPointwise
import OAI.NumberTheory.DirichletL.Hecke.DyadicScale

noncomputable section
open scoped Classical Topology ContDiff ComplexConjugate
open Set Metric Complex MeasureTheory Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorDyadic
open OAI.SevenEighths.Angular.Dyadic FamilyContinuation PhysicalLogarithmic
open PhysicalReciprocal (presentationComplexity)
open HeckeDeletionBounds
open HeckeDyadic (radical_dvd)
theorem radical_norm_le_modulus (χ : AngularCharacter) :
    ((radical χ.modulus).absNorm : ℝ)≤χ.modulus.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot))
    (map_dvd Ideal.absNorm (radical_dvd χ.modulus χ.modulus_ne_bot))

theorem presentationComplexity_le_of_modulus_le (χ : AngularCharacter) (U H : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) :
    presentationComplexity χ H≤2*U^2*(3+|H|)^2 := by
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hU : 0≤U := (Nat.cast_nonneg χ.modulus.absNorm).trans hQ
  unfold presentationComplexity complexity
  calc
    _ ≤ U*(2*U*(3+|H|)^2) := by gcongr
    _ = _ := by ring

theorem reflected_conductor_cost (χ : AngularCharacter) (U a e ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤U) (ha : 1/2≤a) (he : 0≤e) (hε : 0≤ε) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)≤U^(a-1/2+12*e+2*ε) := by
  have hU : 0<U := lt_of_lt_of_le zero_lt_one
    ((PhysicalLogarithmic.modulus_norm_ge_one χ).trans hQ)
  have hR := (radical_norm_le_modulus χ).trans hQ
  calc
    _ ≤ U^(a-1/2+6*e)*U^(6*e+2*ε) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hQ (by linarith))
        (Real.rpow_le_rpow (by positivity) hR (by positivity))
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hU.le _)
    _ = _ := by
      rw [←Real.rpow_add hU]
      congr 1
      ring

end OAI.SevenEighths.Angular.PhysicalDetectorDyadic


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.radical_norm_le_modulus
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.radical_norm_le_modulus

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.presentationComplexity_le_of_modulus_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.presentationComplexity_le_of_modulus_le

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.reflected_conductor_cost
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.reflected_conductor_cost
