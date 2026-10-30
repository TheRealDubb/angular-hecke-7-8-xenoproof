import AngularPhysicalNaturalBandTransport
import AngularPhysicalJointEnergyBottom
import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
import OAI.NumberTheory.DirichletL.Energy.StageMargins
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.NaturalWidth
open EnergyState EnergyBands RelativePrime QuadraticInitialBound NaturalBandTransport
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInduction
  (bandWidth bandWidth_le bandWidth_le_schedule bandWidth_nonneg bandWidth_terminal)
open CenteredMomentEnergyBandMonotonicity (profile_control_mono)
local notation "O"=>ActualEisensteinCubic.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (angularOrder:ℕ)
theorem actual_joint_floor (Mcap B κ ε:ℝ)(hMcap:0≤Mcap)(hB:0≤B)
    (hκ0:0≤κ)(hε:0<ε)
    (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L lo hi:ℝ)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)
    (hκ:(3/4:ℝ)≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀η₀:AngularCharacter,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        ZeroAt angularOrder (internalQ Q η₀) a b bΦ Bmask L (width Mcap B ε 0)
          (loss Mcap B ε 0) Z degree S Czero ∧
        PositiveAt (α:=α) M H hH angularOrder W bslot a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
          (width Mcap B ε 0) (loss Mcap B ε 0) κ Z η₀ Q degree S Cpositive :=by
  have hs:=bounds Mcap B κ ε hMcap hB hκ0 hε
  simpa only [width_zero,loss_zero] using
    exists_joint_bottom (α:=α) M H hH angularOrder W aslot bslot haslot hWs hW
      a b bΦ Bmask L (mesh Mcap B κ ε) lo hi (reserve Mcap B ε) κ
      ha hb hbΦ hmask hs.2.2.2.1 hs.2.2.2.2.1.le hκ

end OAI.SevenEighths.Angular.NaturalWidth

#print axioms OAI.SevenEighths.Angular.NaturalWidth.actual_joint_floor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.actual_joint_floor
