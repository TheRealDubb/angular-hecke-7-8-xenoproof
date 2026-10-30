import AngularPhysicalSourceMomentData
import AngularPhysicalDetectorZeros
import AngularFiniteIdentification

/- The actual finite ray family is a literal subfamily of the angular
   detector dictionary. Only this subfamily is used by the finite prime
   theorem; the angular denominator is retained in the containing maximum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (rayCubeFamily)
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem literal_ray_nonprincipal (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (η : AngularCharacter) (u : FreeRow)
    (hnp : ∀ j, (SourceRows.sourceDetectorFamily M H hH S hS η u j).k ≠ 0 ∨
      (SourceRows.sourceDetectorFamily M H hH S hS η u j).residue ≠ 1) :
    ∀ θ, (rayCubeFamily M H hH u θ).residue ≠ 1 := by
  intro θ
  have hh := hnp (Sum.inr θ)
  change (0:ℤ)≠0 ∨ (rayCubeFamily M H hH u θ).residue≠1 at hh
  exact hh.resolve_left (by simp)

theorem literal_ray_maximum_le (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (η : AngularCharacter) (u : FreeRow)
    (hnp : ∀ j, (SourceRows.sourceDetectorFamily M H hH S hS η u j).k ≠ 0 ∨
      (SourceRows.sourceDetectorFamily M H hH S hS η u j).residue ≠ 1)
    (hray : ∀ θ, (rayCubeFamily M H hH u θ).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hray T ≤
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M H hH S hS η u) hnp T := by
  by_cases hm : (51/100:ℝ) < HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hray T
  · obtain ⟨θ,s,hz,ht,heq⟩ := HeckeDetectorZeros.maximum_attained
      (rayCubeFamily M H hH u) hray T hm
    have hs : (51/100:ℝ) ≤ s.re := by rw [heq]; exact hm.le
    have h0 : s ≠ 0 := by intro he; norm_num [he] at hs
    have h1 : s ≠ 1 := by
      intro he
      exact HeckeFamily.LFunction_one_ne_zero_nonprincipal _ (hray θ) (he ▸ hz)
    have hz' : FamilyContinuation.LFunction
        (SourceRows.sourceDetectorFamily M H hH S hS η u (Sum.inr θ)) s = 0 := by
      change FamilyContinuation.LFunction (AngularCharacter.ofFinite (rayCubeFamily M H hH u θ)) s = 0
      rw [FiniteIdentification.ofFinite_LFunction _ s h0 h1]
      exact hz
    rw [←heq]
    exact PhysicalDetectorZeros.zero_re_le_maximum
      (SourceRows.sourceDetectorFamily M H hH S hS η u) hnp T (Sum.inr θ) hs ht hz'
  · exact (le_of_not_gt hm).trans (PhysicalDetectorZeros.zeroMaximum_bounds _ hnp T).1

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_ray_nonprincipal
#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_ray_maximum_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_ray_maximum_le
