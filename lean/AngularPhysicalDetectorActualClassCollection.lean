import AngularPhysicalDetectorCountedCentralCells
import OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeInverseAmplification (FreeRow)
open ProbePhysical ProbeMellinBoundary ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O

lemma cubeArithmeticSum_image_partition {N : ℕ} {Row Bin : Type*}
    [DecidableEq Row] [Fintype Bin] [DecidableEq Bin]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (rows : Finset Row) (f : Row→FreeRow) (hf : Function.Injective f)
    (key : Row→Bin) (T : Fin N→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
    (W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ) (a e : ℝ) (t : HeightSpace) :
    cubeArithmeticSum S hS hmax η (rows.image f) T hT W Y a e t=
      ∑b : Bin,cubeArithmeticSum S hS hmax η ((rows.filter (fun u=>key u=b)).image f)
        T hT W Y a e t := by
  unfold cubeArithmeticSum
  simp only [Finset.sum_image hf.injOn]
  have hmap : ∀u∈rows,key u∈(Finset.univ : Finset Bin) := by simp
  exact (Finset.sum_fiberwise_of_maps_to hmap _).symm

/-- Actual amplitude labels partition a fixed window cell at each height.
The finite cardinality is paid once; no uniformity in an unbounded slot count
is claimed. The supplied class bound can be instantiated by the actual
counted central-cell theorem on each subcell of the same window. -/
theorem actual_amplitude_cell_collection {N : ℕ}
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (rows : Finset FreeRow) (cell : Finset rows)
    (T : Fin N→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
    (W : ℝ→ℂ) (Y : Fin N→ℝ) (a e mesh : ℝ) (t : HeightSpace)
    (hm : 0<mesh) (ha : a≤1) (A : ℝ) (hA : 0≤A)
    (hclass : ∀part : Finset rows,part⊆cell → part.Nonempty → ∀g : Fin N→ℝ,
      (∀u∈part,∀j,HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 (Y j)
          ((17/50:ℂ)+t.1.2*Complex.I))=g j) →
      ‖cubeArithmeticSum S hS hmax η (part.image Subtype.val) T hT (fun _=>W) Y a e t‖≤A) :
    ‖cubeArithmeticSum S hS hmax η (cell.image Subtype.val) T hT (fun _=>W) Y a e t‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N*A := by
  let Bin := Fin N→↥(HeckePrimeAmplitudeBins.labels (a-1/2) mesh)
  let key : rows→Bin := fun u j=>⟨HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
    (HeckePrimeRow.canonicalPrimeAmplitude M H u.val.val W 2 (Y j)
      ((17/50:ℂ)+t.1.2*Complex.I)),HeckePrimeAmplitudeBins.amplitude_mem_labels _ _ _ _ hm⟩
  let part (b : Bin) : Finset rows := cell.filter (fun u=>key u=b)
  have hbound (b : Bin) :
      ‖cubeArithmeticSum S hS hmax η ((part b).image Subtype.val) T hT (fun _=>W) Y a e t‖≤A := by
    by_cases hne : (part b).Nonempty
    · apply hclass (part b) (Finset.filter_subset _ _) hne (fun j=>(b j).val)
      intro u hu j
      have he := congrArg (fun k : Bin=>(k j).val) (Finset.mem_filter.mp hu).2
      exact he
    · have he : part b=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa only [he,Finset.image_empty,cubeArithmeticSum,Finset.sum_empty,norm_zero] using hA
  have hcard : Fintype.card Bin≤(HeckeDetectorClassBudget.alphabetBound mesh)^N := by
    have hc := HeckeDetectorClassBudget.labels_card_le (a-1/2) mesh (by linarith) hm
    simpa only [Bin,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using
      Nat.pow_le_pow_left hc N
  rw [cubeArithmeticSum_image_partition S hS hmax η cell Subtype.val Subtype.val_injective key
    T hT (fun _=>W) Y a e t]
  calc
    _ ≤ ∑b : Bin,A := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _=>hbound b))
    _ = (Fintype.card Bin:ℝ)*A := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hA

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.cubeArithmeticSum_image_partition

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_amplitude_cell_collection
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_amplitude_cell_collection
