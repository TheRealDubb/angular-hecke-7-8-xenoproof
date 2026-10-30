import AngularPhysicalCommonMaskSlots
import AngularPhysicalNaturalCharacter
import OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular

noncomputable section
open scoped Classical BigOperators
open Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorJoint
open NaturalRows CommonMask HeckePrimeAnnular
local notation "O" => ActualEisensteinCubic.O
/-- The finite source prime pool with the actual annular support exposed. -/
def annularPool (pool : Finset (Ideal O)) (P : ℝ) : Finset (Ideal O) :=
  pool.filter (fun I=>(I.absNorm:ℝ)/P∈Icc (1:ℝ) 2)

theorem annularPool_subset (pool : Finset (Ideal O)) (P : ℝ) : annularPool pool P⊆pool :=
  Finset.filter_subset _ _

theorem annularPool_ratio (pool : Finset (Ideal O)) (P : ℝ) (I : Ideal O)
    (hI : I∈annularPool pool P) : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2 :=
  (Finset.mem_filter.mp hI).2

theorem naturalSlot_annular_filter (χ : AngularCharacter) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (hW : Function.support W⊆Icc (1:ℝ) 2)
    (P σ t : ℝ) :
    naturalSlot χ (annularPool pool P) (fun I=>ν I*annularWeight W P σ t I) P=
      naturalSlot χ pool (fun I=>ν I*annularWeight W P σ t I) P := by
  unfold naturalSlot annularPool
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases ha : (I.absNorm:ℝ)/P∈Icc (1:ℝ) 2
  · exact if_pos ha
  · rw [if_neg ha]
    have hw : W ((I.absNorm:ℝ)/P)=0 := by
      by_contra hn
      exact ha (hW hn)
    simp [annularWeight,hw]


end OAI.SevenEighths.Angular.PhysicalDetectorJoint

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.annularPool_subset
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.annularPool_subset

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.annularPool_ratio
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.annularPool_ratio

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.naturalSlot_annular_filter
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.naturalSlot_annular_filter
