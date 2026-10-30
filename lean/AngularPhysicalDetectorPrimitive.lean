import AngularPhysicalNaturalPrimitivePresentation
import AngularPhysicalAnalyticEntireness
noncomputable section
open scoped Classical Topology
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorPrimitive
open FamilyContinuation PrimitiveReduction

theorem nonprincipal_primitive_identity (χ:AngularCharacter)
    (hχ:χ.k≠0 ∨ χ.residue≠1) (s:ℂ):
    LFunction χ s=LFunction (primitive χ) s*factors χ s := by
  have hp:=NaturalPrimitive.primitive_nonprincipal χ hχ
  have hl:AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (PhysicalAnalytic.nonprincipal_entire χ hχ)
  have hr:AnalyticOnNhd ℂ (fun z=>LFunction (primitive χ) z*factors χ z) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((PhysicalAnalytic.nonprincipal_entire (primitive χ) hp).mul (factors_differentiable χ))
  have he:LFunction χ =ᶠ[𝓝 (3:ℂ)] (fun z=>LFunction (primitive χ) z*factors χ z) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (3:ℂ)∈{z:ℂ | 1<z.re})] with z hz
    rw [LFunction_eq_series χ z hz,LFunction_eq_series (primitive χ) z hz]
    exact series_eq_primitive_mul_factors χ z hz
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr isPreconnected_univ (Set.mem_univ (3:ℂ))
    he (Set.mem_univ s)

end OAI.SevenEighths.Angular.PhysicalDetectorPrimitive

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorPrimitive.nonprincipal_primitive_identity
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorPrimitive.nonprincipal_primitive_identity
