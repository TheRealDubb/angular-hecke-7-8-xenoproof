import AngularPhysicalMarkedDeletedSource
import AngularPhysicalMarkedShift

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Angular.MarkedReference
open InverseRows OAI.SevenEighths.Angular.Dyadic CubicEisenstein.AngularRawCoefficientGates
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
open InverseInitialExcludedPeriod
local notation "O" => HeckeFamily.O

theorem physical_rows_le_deleted_sources {ι : Type*} [Fintype ι]
    (data : RowData) (rows : Finset NonzeroElement)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (W : ℝ → ℂ) (V : ι → ℝ → ℂ) (U r σ freq bW : ℝ)
    (a b ell : ι → ℝ) (ζ : ι → ℂ) (hU : 1 < U)
    (hW : ∀ x, W x ≠ 0 → x ≤ bW)
    (hV : ∀ i x, V i x ≠ 0 → x ∈ Set.Icc (a i) (b i))
    (hlarge : ∀ i, ((deletedBase data).modulus.absNorm : ℝ) < a i * U^(ell i)) :
    (∑ u ∈ rows, ‖polynomial (data.character u) true W (U^r) σ freq *
      (∏ i, HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i)
        (U^(ell i)) (ζ i))‖^2) ≤
      ((idealDivisors (∏ P ∈ excluded data, P)).card : ℝ) *
        ∑ j ∈ idealDivisors (∏ P ∈ excluded data, P), ∑ u ∈ rows,
          ‖deletedSelectedSource data M H W V U (shiftedExponent data U r j)
            σ freq bW b ell ζ u.val‖^2 := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  let mark : NonzeroElement → ℂ := fun u =>
    ∏ i, HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (U^(ell i)) (ζ i)
  apply (marked_fixed_deletion data rows W (U^r) σ freq bW
    (Real.rpow_pos_of_pos hU0 _) hW mark).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro u hu
  have hjpos : 0 < (j.absNorm : ℝ) :=
    zero_lt_one.trans_le (excluded_divisor_norm data j hj).1
  have hr : U^(shiftedExponent data U r j) = U^r / (j.absNorm : ℝ) := by
    rw [shiftedExponent, Real.rpow_sub hU0, Real.rpow_logb hU0 hU.ne' hjpos]
  have hn := deleted_physical_slots_norm_initial data u M H W V U
    (shiftedExponent data U r j) σ freq bW a b ell ζ hU0 hW hV hlarge
  rw [hr] at hn
  exact congrArg (fun x : ℝ => x^2) hn

#print axioms physical_rows_le_deleted_sources
end SevenEighths.Angular.MarkedReference
end
end OAI
