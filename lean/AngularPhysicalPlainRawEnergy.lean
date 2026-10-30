import AngularPhysicalPlainAllocation
import OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy

noncomputable section
open scoped BigOperators Classical
namespace OAI.SevenEighths.Angular.PlainRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentRectangle
open CenteredMomentDivisorRawEnergy (normalized_norm_sq)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [instι : Fintype ι] [decι : DecidableEq ι]

open CenteredMomentDivisorSlots (selectedDivisor_empty)
open IdealMobiusDivisorSum

theorem selected_slot_exact (η : AngularCharacter) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [ite_eq_right hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : AngularCharacter) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem allocated_slot_bound (η : AngularCharacter) (m A z : O) (t : ℝ)
    (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ M)
    (hN : ∀ I ∈ S, β I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ H) :
    ‖rowSlot η m A z S (fun I => if selectedDivisor D s a i∣I then β I else 0) t‖ ≤
      if (selectedPrimes D s a i).Nonempty then M else 128*M*H := by
  by_cases hn : (selectedPrimes D s a i).Nonempty
  · rw [ite_eq_left hn]
    obtain ⟨P,hP⟩ := hn
    exact selected_slot_bound η m A z t (selectedDivisor D s a i) P (support_prime P.property)
      (Finset.dvd_prod_of_mem _ hP) S hS β M hM hβ
  · rw [ite_eq_right hn]
    have he := selectedDivisor_empty D s a i (Finset.not_nonempty_iff_eq_empty.mp hn)
    simp only [he,one_dvd,ite_true]
    exact rowSlot_bound η m A z S β t H M hH hM hβ hN

theorem selected_live_slot (η : AngularCharacter) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ liveIndices D a) (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t =
      rowSlot η m A z S β t := by
  have he := selectedDivisor_empty D Finset.univ a (Sum.inl i)
    (Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hi).2)
  simp only [selectedSlot,he,one_dvd,ite_true]

theorem selected_frozen_slot_bound (η : AngularCharacter) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) (hi : i ∈ frozenIndices D a) (S : Finset (Ideal O))
    (hS : ∀ I∈S,Prime I) (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hβ : ∀ I∈S,‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if selectedSlot D a i∣I then β I else 0) t‖ ≤ M := by
  obtain ⟨P,hP⟩ := (Finset.mem_filter.mp hi).2
  exact selected_slot_bound η m A z t (selectedSlot D a i) P
    (IdealMobiusDivisorSum.support_prime P.property) (Finset.dvd_prod_of_mem _ hP)
    S hS β M hM hβ

theorem selected_slot_product_bound (η : AngularCharacter) (m A z : O) (t : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M : ι → ℝ) (hM : ∀ i,0 ≤ M i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i) :
    (∏ i,‖rowSlot η m A z (S i) (fun I => if selectedSlot D a i∣I then β i I else 0) t‖) ≤
      (∏ i∈frozenIndices D a,M i)*∏ i∈liveIndices D a,‖rowSlot η m A z (S i) (β i) t‖ := by
  rw [← split_slot_product D a]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i hi
    exact selected_frozen_slot_bound η m A z t D a i hi (S i) (hS i) (β i) (M i) (hM i) (hβ i)
  · apply le_of_eq
    apply Finset.prod_congr rfl
    intro i hi
    rw [selected_live_slot η m A z t D a i hi]
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact Finset.prod_nonneg (fun i _ => hM i)

def residualCenteredRow (η : AngularCharacter) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  centeredSlotRow η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
    (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1))
    (T/selectedNorm D a)

theorem allocated_raw_energy (η : AngularCharacter) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 := by
  let R : ℂ :=
    rowTwistedSum η m A z W₁ t (X₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (X₂/Ideal.absNorm (selectedPlain D a 1))-
    rowTwistedSum η m A z W₁ t (Y₁/Ideal.absNorm (selectedPlain D a 0))*
      rowTwistedSum η m A z W₂ t (Y₂/Ideal.absNorm (selectedPlain D a 1))
  let L : ℂ := R*∏ i∈liveIndices D a,rowSlot η m A z (S i) (β i) t
  have hn : ‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖ ≤
      (∏ i∈frozenIndices D a,M i)*‖L‖ := by
    apply (allocatedRectangle_norm_le η m A z t S β D a W₁ W₂ b₁ b₂
      _ _ _ _ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).trans
    have hh := mul_le_mul_of_nonneg_left
      (selected_slot_product_bound η m A z t D a S hS β M hM hβ) (norm_nonneg R)
    dsimp only [L]
    rw [norm_mul,norm_prod]
    convert hh using 1 ; ring
  have hraw : 0 < rawRemaining D a T P := mul_pos (div_pos hT (selectedNorm_pos D a))
    (Finset.prod_pos (fun i _ => hP i))
  have hformal : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hres : ‖residualCenteredRow η m A z t S β P D a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2 =
      ‖L‖^2/rawRemaining D a T P := by
    unfold residualCenteredRow centeredSlotRow
    rw [Finset.prod_coe_sort (liveIndices D a) P,
      Finset.prod_coe_sort (liveIndices D a) (fun i => rowSlot η m A z (S i) (β i) t)]
    exact normalized_norm_sq _ hraw L
  rw [normalized_norm_sq _ htotal,hres]
  calc
    _ ≤ ((∏ i∈frozenIndices D a,M i)*‖L‖)^2/(T*∏ i,P i) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) htotal.le
    _ = _ := by
      rw [← raw_scale_identity D a T P,mul_pow]
      field_simp [hraw.ne',hformal.ne']


end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.allocated_raw_energy
