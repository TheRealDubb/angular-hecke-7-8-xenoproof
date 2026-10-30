import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

noncomputable section
namespace OAI.SevenEighths.Angular.RelativePrime

/-- The original finite-order theorem bounds the finite zero supremum.
This statement says nothing about zeros of nonzero angular type. -/
theorem finite_beta_le_seven_eighths :
    HeckeZeroSupremum.beta ≤ (7/8 : ℝ) := by
  apply csSup_le HeckeZeroSupremum.zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · obtain ⟨χ, s, _, hpole, hzero, rfl⟩ := hx
    by_contra h
    apply HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re χ
      (lt_of_not_ge h) ?_ hzero
    rintro ⟨hχ, hs⟩
    rcases hpole with hn | hn
    · exact hn hs
    · exact hn hχ

theorem seven_eighths_prime_ceiling :
    (51/100 : ℝ) ≤ 7/8 ∧ (7/8 : ℝ) ≤ 1 ∧
      HeckeZeroSupremum.beta ≤ 7/8 ∧ 2*(7/8 : ℝ)-1=3/4 := by
  exact ⟨by norm_num, by norm_num, finite_beta_le_seven_eighths, by norm_num⟩

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.finite_beta_le_seven_eighths
#check OAI.SevenEighths.Angular.RelativePrime.finite_beta_le_seven_eighths
#print axioms OAI.SevenEighths.Angular.RelativePrime.seven_eighths_prime_ceiling
#check OAI.SevenEighths.Angular.RelativePrime.seven_eighths_prime_ceiling
