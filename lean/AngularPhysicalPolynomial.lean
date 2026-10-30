import AngularInverseRows
import AngularPrimeDeletion

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.Angular.Dyadic


abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def norm (I : NonzeroIdeal) : ℝ := I.val.absNorm

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

def coefficient (χ : AngularCharacter) (inverse : Bool) (I : Ideal O) : ℂ :=
  if inverse then (UniqueFactorizationMonoid.moebius I : ℂ)*χ.idealHom I else χ.idealHom I

theorem coefficient_norm_le (χ : AngularCharacter) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact χ.norm_idealHom_le_one I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*χ.idealHom I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (χ.norm_idealHom_le_one I)

@[simp] theorem coefficient_zero (χ : AngularCharacter) (inverse : Bool) : coefficient χ inverse 0 = 0 := by
  cases inverse
  · exact map_zero χ.idealHom
  · change (UniqueFactorizationMonoid.moebius (0 : Ideal O) : ℂ)*χ.idealHom 0 = 0
    rw [map_zero, mul_zero]

def shift (σ ω : ℝ) : ℂ := (σ : ℂ)-(ω : ℂ)*Complex.I

@[simp] theorem shift_re (σ ω : ℝ) : (shift σ ω).re = σ := by simp [shift]

def summand (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ)
    (D σ ω : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ ω)

def polynomial (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ inverse W D σ ω I

theorem summand_finite_support (χ : AngularCharacter) (inverse : Bool) (W : ℝ → ℂ)
    (a b D σ ω : ℝ) (hD : 0 < D) (hW : Function.support W ⊆ Icc a b) :
    (Function.support (summand χ inverse W D σ ω)).Finite := by
  have hfin := Ideal.finite_setOfPred_absNorm_le (S := O) ⌈D*b⌉₊
  apply (Set.Finite.preimage (f := fun I : NonzeroIdeal => I.val) Subtype.val_injective.injOn hfin).subset
  intro I hI
  have hw : W (norm I/D) ≠ 0 := by
    intro h
    exact hI (by simp [summand, h])
  have hupper := (hW hw).2
  have hq : norm I ≤ D*b := by
    have h := (div_le_iff₀ hD).mp hupper
    linarith
  have hr : norm I ≤ (⌈D*b⌉₊ : ℝ) := hq.trans (Nat.le_ceil _)
  change I.val.absNorm ≤ ⌈D*b⌉₊
  dsimp [norm] at hr
  exact_mod_cast hr

#print axioms coefficient_norm_le
#print axioms summand_finite_support
end SevenEighths.Angular.Dyadic
end
end OAI
