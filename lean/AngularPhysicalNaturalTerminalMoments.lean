import AngularPhysicalNaturalCertifiedExistence
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.NaturalWidth
open EnergyState EnergyBands RelativePrime QuadraticInitialBound NaturalBandTransport
open NaturalReference NaturalStage
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInduction
  (bandWidth bandWidth_nonneg bandWidth_le)
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyCappedRequests
open CenteredMomentEnergySourceCapSchedule
local notation "O"=>ActualEisensteinCubic.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (angularOrder:ℕ)
theorem terminal_actual_bands
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    :
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:AngularCharacter,η₀.k.natAbs=angularOrder→
    ∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ZeroAt angularOrder (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
      PositiveAt (α:=α) M H hH angularOrder W bslot a b radial Bmask L
        (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S Cpositive:=by
  apply certified_terminal (α:=α) M H hH angularOrder W bslot a b radial Bmask L lo hi Mcap κ ε
    hmask hMcap.le (by linarith) hε
  exact certified_bands (α:=α) M H hH angularOrder W aslot bslot a b radial Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε _ le_rfl

end OAI.SevenEighths.Angular.NaturalWidth


#print axioms OAI.SevenEighths.Angular.NaturalWidth.terminal_actual_bands
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.terminal_actual_bands
