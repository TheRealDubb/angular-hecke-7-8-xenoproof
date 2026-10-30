import AngularPhysicalDetectorLiteralRayMaximum
import OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins

/- The finite theorem below is used only for an actual finite member of the
angular source family. The angular denominator is not made periodic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalDetectorNumerator
open HeckeInverseAmplification (FreeRow)
local notation "O" => HeckeFamily.O

theorem finite_member_maximum_le {Label : Type*} [Fintype Label]
    (χ : Label → AngularCharacter)
    (hnp : ∀ j, (χ j).k ≠ 0 ∨ (χ j).residue ≠ 1)
    (j : Label) (ψ : HeckeFamily.Character) (hj : χ j = AngularCharacter.ofFinite ψ)
    (T : ℝ) :
    ProbeHighRowFamily.detectorMaximum (fun _ : Unit => ψ) T ≤
      PhysicalDetectorZeros.zeroMaximum χ hnp T := by
  have hψ : ψ.residue ≠ 1 := by
    have h := hnp j
    rw [hj] at h
    change (0:ℤ) ≠ 0 ∨ ψ.residue ≠ 1 at h
    exact h.resolve_left (fun h0 => h0 rfl)
  by_cases hm : (51/100:ℝ) < ProbeHighRowFamily.detectorMaximum (fun _ : Unit => ψ) T
  · obtain ⟨_,s,hz,_,ht,heq⟩ :=
      ProbeHighRowFamily.detectorMaximum_attained (fun _ : Unit => ψ) T hm
    have hs : (51/100:ℝ) ≤ s.re := by rw [heq]; exact hm.le
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by
      intro h
      exact HeckeFamily.LFunction_one_ne_zero_nonprincipal ψ hψ (h ▸ hz)
    have hz' : FamilyContinuation.LFunction (χ j) s = 0 := by
      rw [hj,FiniteIdentification.ofFinite_LFunction ψ s h0 h1]
      exact hz
    rw [←heq]
    exact PhysicalDetectorZeros.zero_re_le_maximum χ hnp T j hs ht hz'
  · exact (le_of_not_gt hm).trans (PhysicalDetectorZeros.zeroMaximum_bounds χ hnp T).1

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem literal_numerator_maximum_le (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow)
    (hnp : ∀ j, (SourceRows.sourceDetectorFamily M H hH S hS η u j).k ≠ 0 ∨
      (SourceRows.sourceDetectorFamily M H hH S hS η u j).residue ≠ 1)
    (T : ℝ) :
    ProbeHighRowFamily.detectorMaximum (fun _ : Unit => ProbeHighRowFamily.rowCharacter S hS u) T ≤
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M H hH S hS η u) hnp T :=
  finite_member_maximum_le _ hnp (Sum.inl true) _ rfl T

end OAI.SevenEighths.Angular.PhysicalDetectorNumerator
#print axioms OAI.SevenEighths.Angular.PhysicalDetectorNumerator.finite_member_maximum_le
#print axioms OAI.SevenEighths.Angular.PhysicalDetectorNumerator.literal_numerator_maximum_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorNumerator.literal_numerator_maximum_le
