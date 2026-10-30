import AngularPhysicalPlainAllocation
import OAI.NumberTheory.DirichletL.Moments.DivisorActualBoundary

noncomputable section
open scoped BigOperators Classical
namespace OAI.SevenEighths.Angular.PlainRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [instι : Fintype ι] [decι : DecidableEq ι]

open CenteredMomentDivisorRaw CenteredMomentSlotRatios
open CenteredMomentDivisorWitness (actualExtracted_norm_boundary)
open CenteredMomentDivisorActualBoundary (selected_log_identity)

private theorem exists_tsum_term {α : Type*} (f : α → ℂ) (h : (∑' x,f x) ≠ 0) :
    ∃ x,f x ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [hn,tsum_zero])

theorem allocated_nonzero_witness (η : AngularCharacter) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    ∃ (v : (i : ι) → S i) (I J : Ideal O),
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a ≠ 0 ∧
      (∀ i,β i (v i) ≠ 0) ∧ idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0 := by
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hβ,ht⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨I,hI⟩ := exists_tsum_term _ ht
  obtain ⟨J,hJ⟩ := exists_tsum_term _ hI
  have hh := mul_ne_zero_iff.mp hJ
  exact ⟨v,I,J,(mul_ne_zero_iff.mp hh.1).1,
    fun i => Finset.prod_ne_zero_iff.mp hβ i (Finset.mem_univ i),hh.2⟩

theorem nonzero_row_formal_boundary (η : AngularCharacter) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (hβW : ∀ i I,β i I ≠ 0 → W i ((Ideal.absNorm I:ℝ)/P i) ≠ 0)
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨v,I,J,ha,hβ,hrect⟩ := allocated_nonzero_witness η m A z t S β D a
    W₁ W₂ X₁ X₂ Y₁ Y₂ hne
  have hv (i : ι) : (v i:Ideal O) ≠ 0 := (hS i (v i) (v i).property).ne_zero
  have hb := actualExtracted_norm_boundary D hD a (fun i => v i) hv I J ha
  have hND : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hl := Real.logb_le_logb_of_le hZ hND hb
  rw [selected_log_identity D a (fun i => v i) hv P hP Z] at hl
  have hr : |∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i)| ≤
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
    apply frozen_subset_ratio_bound (ι := ι) Finset.univ (frozenIndices D a) (Finset.subset_univ _)
      W lo hi P (fun i => (v i:Ideal O)) Z hZ
    · intro i _
      exact hlo i
    · intro i _
      exact hW i
    · intro i _
      exact hβW i (v i) (hβ i)
  have hh := (le_abs_self (∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i))).trans hr
  linarith

theorem original_nonzero_row_formal_boundary (η : AngularCharacter) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z :=
  nonzero_row_formal_boundary η m A z t S hS _ W lo hi P hlo hP hW
    (fun _i _I h => (mul_ne_zero_iff.mp h).2) D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hne


end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.original_nonzero_row_formal_boundary
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.original_nonzero_row_formal_boundary
