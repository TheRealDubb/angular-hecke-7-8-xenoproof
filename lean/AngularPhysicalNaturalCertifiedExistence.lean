import AngularPhysicalNaturalCappedSuccessor
import AngularPhysicalNaturalCappedRadialTransport

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.Angular.NaturalWidth
open EnergyState EnergyBands RelativePrime QuadraticInitialBound NaturalBandTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=>ActualEisensteinCubic.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

variable (angularOrder : ℕ)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    :
    ∀k:ℕ,k≤count Mcap ε→
      CertifiedBand (α:=α) M H hH angularOrder W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH angularOrder W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hκ0
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k<count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH angularOrder W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(_hrad:0<radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    :
    CertifiedBand (α:=α) M H hH angularOrder W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH angularOrder W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH angularOrder W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε _ le_rfl

end SevenEighths.Angular.NaturalWidth

end

end OAI

#print axioms OAI.SevenEighths.Angular.NaturalWidth.certified_bands
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.certified_bands

#print axioms OAI.SevenEighths.Angular.NaturalWidth.terminal_certificate
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.terminal_certificate
