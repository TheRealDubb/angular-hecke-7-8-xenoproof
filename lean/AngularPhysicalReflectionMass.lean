import AngularPhysicalPlainDeletedReflection
import OAI.NumberTheory.DirichletL.Moments.ReflectionMass

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ReflectionMass
open CenteredMomentReflectionDeletion (SmoothIdeal norm subset_product_moebius)
open CenteredMomentReflectionMass (weight smooth_summable smooth_mass_le_euler weight_nonneg
  deletion_mass localMass euler_mass_subpower unitSmooth)
open PlainDeletion (reflectedTerm)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def coefficient (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * η.idealHom (∏ P ∈ D,P) * ηi.idealHom H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P):ℝ) * norm H.val) : ℂ)

lemma coefficient_norm_le (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (hD : ∀ P ∈ D,Prime P) (H : SmoothIdeal S) :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖η.idealHom (∏ P ∈ D,P)‖ * ‖ηi.idealHom H.val.val‖ ≤ 1 :=
    (mul_le_mul (η.norm_idealHom_le_one _) (ηi.norm_idealHom_le_one _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

lemma coefficient_summable_norm (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP)) H

lemma coefficient_summable (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (coefficient η ηi S D) := (coefficient_summable_norm η ηi S hS D hD).of_norm

lemma coefficient_mass_le_euler (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := by
  exact summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : AngularCharacter),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

lemma coefficient_empty_unit (η ηi : AngularCharacter) (S : Finset (Ideal O)) :
    coefficient η ηi S ∅ (unitSmooth S) = 1 := by
  have hm : (moebius (1 : Ideal O) : ℂ) = 1 := by
    simpa only [Finset.prod_empty,Finset.card_empty,pow_zero] using
      subset_product_moebius ∅ (by simp)
  change (moebius (1 : Ideal O) : ℂ) * η.idealHom 1 * ηi.idealHom 1 /
    (Real.sqrt ((Ideal.absNorm (1 : Ideal O) : ℝ) * (Ideal.absNorm (1 : Ideal O) : ℝ)) : ℂ) = 1
  rw [hm,map_one,map_one,map_one]
  norm_num

lemma reflectedTerm_eq_coefficient (η ηi : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H = coefficient η ηi S D H *
      Dyadic.polynomial (ηi.excludePrimes S hS) false F
        (Q * (Ideal.absNorm (∏ P ∈ D,P):ℝ)/(X*norm H.val)) 0 0 := rfl


end OAI.SevenEighths.Angular.ReflectionMass

#print axioms OAI.SevenEighths.Angular.ReflectionMass.reflection_mass_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionMass.reflection_mass_subpower
