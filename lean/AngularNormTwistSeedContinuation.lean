import AngularNormTwistContinuation
import AngularSeedNonvanishing

/- Legacy 23/24 seed corollary, moved verbatim out of the public 7/8 import closure. -/
noncomputable section
open scoped Classical Topology
open Complex
namespace OAI.SevenEighths.Angular.NormTwist

theorem physical_seed_all_norm_twists (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re) (hpole : χ.k = 0 → s ≠ 1+(τ:ℂ)*I) :
    LFunction χ τ s ≠ 0 := by
  apply (halfPlane_transport_iff χ τ ((23:ℝ)/24)).mp
    (OAI.CubicEisenstein.AngularSeedNonvanishing.physical_seed_all_types χ) s hs hpole

end OAI.SevenEighths.Angular.NormTwist
