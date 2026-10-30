import AngularPhysicalReflectionColumn
import AngularPhysicalReflectedSeries
import AngularPhysicalPlainRapidDecay
import OAI.NumberTheory.DirichletL.Moments.RetainedReflection

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.RetainedReflection
open CenteredMomentReflectionDeletion (DecayTwo SmoothIdeal norm norm_pos subset_product_norm_pos)
open CenteredMomentRetainedReflection (masked_decayTwo)
open CenteredMomentReflectionTailMass (dual_scale_bounds)
open CenteredMomentComparisonReflection (normalized_power_eq)
open CenteredMomentSectorLocalization
open PlainDeletion (polynomial_plain)
open ReflectedSeries (plain_summable)
open ReflectionMass
open ReflectionTails (plain_rapid_bound)
local notation "O" => ActualEisensteinCubic.O

lemma column_retained_discarded (η : AngularCharacter) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    Dyadic.polynomial η false F Y 0 0=
      Dyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0+
      Dyadic.polynomial η false (fun x=>(discardedWeight R x:ℂ)*F x) Y 0 0 := by
  have hr := plain_summable η _ (masked_decayTwo F hF _ (retainedWeight_bounds R)) Y hY
  have hd := plain_summable η _ (masked_decayTwo F hF _ (discardedWeight_bounds R)) Y hY
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,
    ←mul_add,←hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro I
  have hp := retained_add_discarded R (norm I/Y) (div_pos (norm_pos I) hY)
  simp only [CenteredMomentReflectionDeletion.norm] at hp ⊢
  rw [←mul_add,←add_mul,←Complex.ofReal_add,hp,Complex.ofReal_one,one_mul]

lemma bounded_columns (η : AngularCharacter) (F : ℝ→ℂ) (hF : DecayTwo F) :
    ∃C : ℝ,0≤C ∧ ∀Y U : ℝ,0<Y → Y≤U →
      ‖Dyadic.polynomial η false F Y 0 0‖≤C*U^(3/2:ℝ) := by
  obtain ⟨D,hD,hF⟩ := hF
  obtain ⟨C,hC,hb⟩ := plain_rapid_bound 2 (by omega)
  refine ⟨C*D,by positivity,?_⟩
  intro Y U hY hYU
  apply (hb η F D Y hD hY hF).trans
  rw [normalized_power_eq Y hY 2]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY.le hYU (by norm_num)) (by positivity)

lemma reflected_column_summable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η ηi χ : AngularCharacter) (F : ℝ→ℂ) (hF : DecayTwo F) (Q X : ℝ)
    (hQ : 0<Q) (hX : 0<X) (D : Finset (Ideal O)) (hD : D∈S.powerset) :
    Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
      Dyadic.polynomial χ false F
        (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0) := by
  obtain ⟨C,hC,hb⟩ := bounded_columns χ F hF
  obtain ⟨K,hK,hKb⟩ := coefficient_column_bound 1 (by norm_num)
  let U := Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X
  have hu : 0<U := div_pos (mul_pos hQ (subset_product_norm_pos S hS)) hX
  exact (hKb S hS η ηi (fun E H=>Dyadic.polynomial χ false F
    (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*U^(3/2:ℝ)) (by positivity) (by
      intro E hE H
      have hscale := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X U hQ hX (by
        dsimp [U]
        rw [div_mul_cancel₀ _ hX.ne'])
      exact hb _ U hscale.1 hscale.2)).1 D hD


end OAI.SevenEighths.Angular.RetainedReflection

#print axioms OAI.SevenEighths.Angular.RetainedReflection.reflected_column_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedReflection.reflected_column_summable
