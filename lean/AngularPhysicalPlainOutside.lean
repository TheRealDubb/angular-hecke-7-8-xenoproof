import AngularPrimeDeletion
import AngularPhysicalPlainAbsolute
import OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainDeletion
open CenteredMomentReflectionDeletion (DecayTwo norm norm_pos outside outside_iff_coprime
  radial_summable_norm outside_mul_prime subset_product_nonzero subset_product_norm_pos
  normalization_factor subset_product_moebius schwartz_decayTwo)
open CenteredMomentComparisonReflection (inverse_half_power)
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma polynomial_plain (η : AngularCharacter) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    Dyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,η.idealHom I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [Dyadic.polynomial,Dyadic.summand,Dyadic.coefficient,
    Bool.false_eq_true,ite_false,Dyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,Dyadic.norm]
  rw [inverse_half_power X hX.le]

lemma deleted_coefficient (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : NI) :
    (η.excludePrimes S hS).idealHom I.val =
      if outside S I.val then η.idealHom I.val else 0 := by
  rw [AngularCharacter.idealHom_excludePrimes, outside_iff_coprime S hS I]
  split_ifs <;> rfl

def outsideSum (η : AngularCharacter) (S : Finset (Ideal O)) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI, (if outside S I.val then η.idealHom I.val else 0) * F (norm I / X)

lemma outsideSum_summable (η : AngularCharacter) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => (if outside S I.val then η.idealHom I.val else 0) * F (norm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (η.norm_idealHom_le_one I.val)
  · simp

lemma prime_shift_tsum (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI, if P ∣ I.val then
      (if outside S I.val then η.idealHom I.val else 0) * F (norm I / X) else 0) =
    η.idealHom P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  let f : NI → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then η.idealHom I.val else 0) * F (norm I / X) else 0
  let g : NI → ℂ := fun I => η.idealHom P *
    ((if outside S I.val then η.idealHom I.val else 0) * F (norm I / (X / (P.absNorm : ℝ))))
  let e : NI → NI := fun I => ⟨P*I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI) : f (e I) = g I := by
    have hn : norm (e I) = (P.absNorm : ℝ) * norm I := by
      simp only [CenteredMomentReflectionDeletion.norm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      map_mul, g]
    change (if outside S I.val then η.idealHom P * η.idealHom I.val else 0) *
      F (norm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J,hJ⟩ := hd
      have hj : J ≠ 0 := by intro hz; exact I.property (by rw [hJ,hz,mul_zero])
      have hei : e ⟨J,hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J,hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J,hj⟩,hg⟩,hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η (insert P S) F X = outsideSum η S F X -
      η.idealHom P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable η S F hF X hX
  have hd : Summable (fun I : NI => if P ∣ I.val then
      (if outside S I.val then η.idealHom I.val else 0) * F (norm I / X) else 0) := by
    exact hs.indicator {I : NI | P ∣ I.val}
  rw [← prime_shift_tsum η S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]


end OAI.SevenEighths.Angular.PlainDeletion

#print axioms OAI.SevenEighths.Angular.PlainDeletion.outsideSum_insert
