import AngularPhysicalDetectorHighSignal
import AngularPhysicalDetectorHighCorrection
import OAI.NumberTheory.DirichletL.Detector.SourceExclusions

namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve ProbePhysical
open FamilyContinuation (LFunction)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem excludedTarget_hasProd (η : AngularCharacter) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} =>
      (1-η.idealHom P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S η.idealHom (SourceRows.excluded_prime η S hS) s hs

theorem excludedIdealHighSeries_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S} => idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) :=
  excludedIdealHighSeries_row_hasProd_outside S hS η 1 x w z hx hw hz

theorem principalHigh_L_factorization (S : Finset Id) (hS : ∀P∈S,Prime P)
    (hgood : ∀P : PrimeIdeal,P.val∉S → Supported P.val) (htail : CorrectionTail S)
    (η : AngularCharacter) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS) (6*z) * HeckeFamily.LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hH := remainder_globalClosedCorrection_multipliable η S htail x w z ((show theta≤3/2 by norm_num [theta]).trans hx.le) (by linarith) (by linarith)
  have he := (((fixedSourcePrincipal_hasProd S hS (6*z) hz1).mul
    (fixedSourcePrincipal_hasProd S hS w hw1)).mul
      ((excludedTarget_hasProd η S hS x hx1).inv₀
        (FamilyContinuation.LFunction_ne_zero (η.excludePrimes S hS) x hx1))).mul hH.hasProd
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ((1-CubicEisenstein.fullIdealWeight (6*z) P.val.val)⁻¹ *
       (1-CubicEisenstein.fullIdealWeight w P.val.val)⁻¹ *
       ((1-η.idealHom P.val.val*CubicEisenstein.fullIdealWeight x P.val.val)⁻¹)⁻¹) *
       idealClosedCorrection η P.val x w z = idealHighLocalFactor η P.val.val x w z := by
    rw [idealHighLocalFactor_rational η P.val (hgood P.val P.property) x w z hx hw hz]
    simp only [CubicEisenstein.fullIdealWeight,P.val.property.ne_zero,ite_false,
      Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [show -(6*z)=(-6:ℂ)*z by ring]
    ring
  have he' : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS) (6*z) * HeckeFamily.LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z) := by
    simpa only [hlocal,div_eq_mul_inv,globalClosedCorrection] using he
  exact (excludedIdealHighSeries_hasProd_outside S hS η x w z hx hw hz).unique he'

/-- The same literal correction that occurs in the initial physical
identity is analytic and nonzero in the auxiliary correction region containing Re(s)>7/8.
The set S is fixed before the angular target and its finite conductor. -/
theorem exists_actual_principal_signal (S₀ : Finset Id)
    (hp : ∀P∈S₀,Prime P) (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,∃hS : SourceExclusions S,S₀⊆S ∧
      ∀η : AngularCharacter,
        (∀x w z : ℂ,3/2<x.re → 2<w.re → 1/6<z.re →
          markedIdealHighSeries S 1 η 1 x w z =
            HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
              HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
              LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) ∧
        AnalyticOnNhd ℂ (fun s => globalClosedCorrection η S s 1 (1/6))
          {s : ℂ | theta<s.re} ∧
        (∀s : ℂ,theta≤s.re → ‖globalClosedCorrection η S s 1 (1/6)-1‖≤1/2 ∧
          globalClosedCorrection η S s 1 (1/6)≠0) := by
  obtain ⟨S,hsub,hS⟩ := exists_source_exclusions S₀ hp hbad
  refine ⟨S,hS,hsub,?_⟩
  intro η
  refine ⟨?_,?_,?_⟩
  · intro x w z hx hw hz
    exact principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad)
      hS.tail η x w z hx hw hz
  · exact remainder_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6)
      (by norm_num) (by norm_num)
  · intro s hs
    exact ⟨remainder_globalClosedCorrection_bound η S hS.tail s 1 (1/6) hs
      (by norm_num) (by norm_num),
      remainder_globalClosedCorrection_ne_zero η S hS.tail s 1 (1/6) hs
      (by norm_num) (by norm_num)⟩

end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.principalHigh_L_factorization

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_principal_signal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.exists_actual_principal_signal
