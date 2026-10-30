import AngularPhysicalPlainRapidDecay

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.ReflectionTails
open AnnularFourier
open PlainDeletion (polynomial_plain)
open CenteredMomentComparisonReflection (ideal_norm_rpow_summable discarded_rapid_control normalized_power_eq)
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem actual_reflected_absolute_bound (angularOrder:ℕ) (a b : ℝ) (ha : 0<a) (B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(η : AngularCharacter)(t Y : ℝ),0<Y →
      ‖Dyadic.polynomial η false
        (profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y) := by
  obtain ⟨n,hn⟩ := absolute_order_height_control angularOrder a b ha B 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro k hk η t Y hY
  have hf : ∀x : ℝ,0<x → x^B*‖profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb k hk t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) B)
      (norm_nonneg _)).trans hh
  exact (hKb η _ (D*(1+‖t‖)^n) Y (by positivity) hY hf).trans_eq (by ring)

theorem actual_reflected_discarded_bound (angularOrder:ℕ) (a b : ℝ) (ha : 0<a) (A B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(η : AngularCharacter)(t Y R : ℝ),0<Y → 0<R →
      ‖Dyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*
          profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨n,hn⟩ := absolute_order_height_control angularOrder a b ha (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro k hk η t Y R hY hR
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb k hk t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*(1+‖t‖)^n) R (by positivity) hR hf
  exact (hKb η _ ((D*(1+‖t‖)^n)/R^A) Y (by positivity) hY hm).trans_eq (by ring)


end OAI.SevenEighths.Angular.ReflectionTails

#print axioms OAI.SevenEighths.Angular.ReflectionTails.actual_reflected_absolute_bound
#print axioms OAI.SevenEighths.Angular.ReflectionTails.actual_reflected_discarded_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionTails.actual_reflected_discarded_bound
