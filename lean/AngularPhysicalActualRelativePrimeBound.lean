import AngularPhysicalRelativePrimeHeight
import AngularPhysicalRelativeRayNonprincipal
import AngularPhysicalRelativePrimeSlot

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter
namespace OAI.SevenEighths.Angular.RelativePrime
open NaturalRows ExceptionalRows CanonicalRowCompletion
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O

variable (M:Ideal O) [NeZero M]
local instance actualRelativePrimeFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

/-- The constant and height degree are chosen before the fixed opposite-type
slot, the live zero ceiling, kappa, parent character, scales and frequencies.
Only the eventual scale threshold may depend on the fixed slot modulus. -/
theorem actual_relative_slot_bound (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hWs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:AngularCharacter,∀ᶠZ:ℝ in atTop,
      ∀ceiling κ:ℝ,(51/100:ℝ)≤ceiling → ceiling≤1 →
      HeckeZeroSupremum.beta≤ceiling → 2*ceiling-1≤κ →
      ∀P:ℝ,1≤P → P≤Z^Lslot → ∀η χ:AngularCharacter,χ.k=η.k → χ.k+ν.k=0 →
      ∀m A z:O,(∀n:O,χ.elementCoeff n=rowTwist η.elementHom.toMonoidHom m 1 (A*z) n) →
      (χ.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q:Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q m A z →
      ∀σ t v:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H b P)
        (fun I=>ν.idealHom I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=ray_prime_ceiling_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi (by linarith) hLs hloss
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (ν.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hν hZ
  intro ceiling κ hfloor hupper hceil hκ P hP hPcap η χ htype hk m A z hrow hcond Q hQM hQν hex σ t v hσ hσhi
  have hc:((finiteProduct χ ν hk).modulus.absNorm:ℝ)≤Z^(Lmod+1):=by
    have hb:((finiteProduct χ ν hk).modulus.absNorm:ℝ)≤
        (χ.modulus.absNorm:ℝ)*(ν.modulus.absNorm:ℝ):=by
      exact_mod_cast finiteProduct_modulus_bound χ ν hk
    apply hb.trans
    calc
      _≤Z^Lmod*Z:=mul_le_mul hcond hν (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1):=by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound ceiling κ hfloor hupper hceil hκ Z P hZ0 hP hPcap (finiteProduct χ ν hk) hc
    (all_relative_ray_twists_nonprincipal M H hH η χ ν htype hk Q m A z hrow hQν hQM hex)
    σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_norm_sq M H η χ ν hk m A z hrow W b P σ t v (zero_lt_one.trans_le hP)]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

/-- A natural angular row satisfies the exact presentation required above.
The signed angular cancellation is retained as an explicit hypothesis. -/
theorem natural_relative_slot_bound (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hWs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:AngularCharacter,∀ᶠZ:ℝ in atTop,
      ∀ceiling κ:ℝ,(51/100:ℝ)≤ceiling → ceiling≤1 →
      HeckeZeroSupremum.beta≤ceiling → 2*ceiling-1≤κ →
      ∀P:ℝ,1≤P → P≤Z^Lslot → ∀η:AngularCharacter,∀z:O,
      ∀F:NaturalRow η z,η.k+ν.k=0 → (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q:Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>ν.idealHom I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi hLm hLs hloss
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν] with Z hb
  intro ceiling κ hfloor hupper hceil hκ P hP hPcap η z F hk hcond Q hQM hQν hex σ t v hσ hσhi
  exact hb ceiling κ hfloor hupper hceil hκ P hP hPcap η F.character F.angular_type
    (by rw [F.angular_type];exact hk) fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) hcond Q hQM hQν hex σ t v hσ hσhi

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.actual_relative_slot_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.actual_relative_slot_bound

#print axioms OAI.SevenEighths.Angular.RelativePrime.natural_relative_slot_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.natural_relative_slot_bound
