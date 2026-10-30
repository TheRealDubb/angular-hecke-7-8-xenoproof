import AngularChosenReflection

/-! Exact separation of the added denominator phase into fixed, row,
and slot factors. Their norms are one for nonzero physical generators.
The dual angular factor depends only on the frequency index. -/

noncomputable section
open scoped Classical BigOperators MatrixGroups
namespace OAI.CubicEisenstein.AngularPhaseSeparation
open ConcreteTraceCRT SevenEighths.Angular AngularControlledScalar
local notation "Eis" => ActualEisensteinCubic.O

def denominatorPhase : Eis →* ℂ where
  toFun c := ((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) / eisEmbedding c ^ 2
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, norm_mul, mul_pow, Complex.ofReal_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem denominatorPhase_norm (c : Eis) (hc : c ≠ 0) : ‖denominatorPhase c‖ = 1 := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  change ‖((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) / eisEmbedding c ^ 2‖ = 1
  rw [norm_div, Complex.norm_of_nonneg (sq_nonneg _), norm_pow]
  exact div_self (pow_ne_zero _ hn)

theorem shapeOrderPhase_factor {H : SL(2,Eis)} (s : FixedCuspShape H) (c : Eis) :
    shapeOrderPhase s c = shapeOrderPhase s 1 * denominatorPhase c := by
  simp only [shapeOrderPhase, map_one, norm_one, one_pow, Complex.ofReal_one, one_mul]
  change _ = _ * (((‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) / eisEmbedding c ^ 2)
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev]
  ring

theorem shapeOrderPhase_mul {H : SL(2,Eis)} (s : FixedCuspShape H) (a b : Eis) :
    shapeOrderPhase s (a*b) = shapeOrderPhase s a * denominatorPhase b := by
  rw [shapeOrderPhase_factor, map_mul, shapeOrderPhase_factor s a]
  ring

theorem physical_row_slot_phase {H : SL(2,Eis)} (s : FixedCuspShape H)
    (c fixed row slot : Eis) (n : ℕ) :
    shapeOrderPhase s (c * (fixed * row * slot)) ^ n =
      shapeOrderPhase s (c * fixed) ^ n * denominatorPhase row ^ n * denominatorPhase slot ^ n := by
  rw [show c * (fixed * row * slot) = ((c*fixed)*row)*slot by ring,
    shapeOrderPhase_mul, shapeOrderPhase_mul, mul_pow, mul_pow]

theorem row_slot_phase_norm (row slot : Eis) (hr : row ≠ 0) (hs : slot ≠ 0) (n : ℕ) :
    ‖denominatorPhase row ^ n * denominatorPhase slot ^ n‖ = 1 := by
  rw [norm_mul, norm_pow, norm_pow, denominatorPhase_norm row hr, denominatorPhase_norm slot hs]
  simp

theorem angular_column_norm (a : Eis) (n : ℕ) : ‖alpha a ^ n‖ ≤ 1 := by
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  by_cases ha : a = 0
  · simp [ha, alpha, FiniteGaussPhase.angularFactor]
  · exact (norm_alpha ha).le

theorem angular_column_product_bound (a : Eis) (n : ℕ) (b : ℂ) :
    ‖b * alpha a ^ n‖ ≤ ‖b‖ := by
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (angular_column_norm a n) (norm_nonneg b)

#print axioms physical_row_slot_phase
#print axioms row_slot_phase_norm
end OAI.CubicEisenstein.AngularPhaseSeparation
