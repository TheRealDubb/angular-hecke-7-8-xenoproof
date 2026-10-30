import AngularPhysicalCommonMaskSlots

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.CommonMask
open PlainDeletion
open CenteredMomentReflectionDeletion (outside subset_product_moebius schwartz_decayTwo)
open CenteredMomentReflectionMass
open CenteredMomentCommonMaskExpansion (outside_prime prod_sub_expansion slotMass
  slotMass_nonneg slotMass_bound coefficientMajorant uniformMajorant uniformMajorant_nonneg
  uniform_mass_subpower)
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

variable {α : Type*} [decα : DecidableEq α]

lemma naturalSlot_norm (χ : AngularCharacter) (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ‖naturalSlot χ (pool∩R) β P‖≤slotMass R pool β P := by
  rw [naturalSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hi
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_idealHom_le_one I)

lemma plainCoefficient_norm (χ : AngularCharacter) (D : Finset (Ideal O))
    (hD : ∀I∈D,Prime I) : ‖plainCoefficient χ D‖≤weight (∏I∈D,I) := by
  rw [plainCoefficient,subset_product_moebius D hD]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (χ.norm_idealHom_le_one _) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [weight,one_div])

lemma signedCoefficient_norm (χ : AngularCharacter) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤coefficientMajorant R D₁ D₂ J pool β P := by
  simp only [signedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
  apply mul_le_mul
  · exact mul_le_mul (plainCoefficient_norm χ D₁ (fun I hi=>hR I (hD₁ hi)))
      (plainCoefficient_norm χ D₂ (fun I hi=>hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
  · exact Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>naturalSlot_norm χ R (pool i) (β i) (P i))
  · positivity
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)


lemma signedCoefficient_uniform (χ : AngularCharacter) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P b M : α→ℝ)
    (hp : ∀i∈J,∀I∈pool i,Prime I) (hP : ∀i∈J,0<P i) (hM : ∀i∈J,0≤M i)
    (hβ : ∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i∈J,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤uniformMajorant R D₁ D₂ J b M := by
  apply (signedCoefficient_norm χ R hR D₁ D₂ hD₁ hD₂ J pool β P).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod₀ (fun i _=>slotMass_nonneg _ _ _ _)
    (fun i hi=>slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))



end OAI.SevenEighths.Angular.CommonMask

#print axioms OAI.SevenEighths.Angular.CommonMask.signedCoefficient_uniform
