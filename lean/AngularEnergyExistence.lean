import AngularEnergyData
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistence

namespace OAI.CubicEisenstein.AngularEnergyExistence
noncomputable section
open scoped Classical BigOperators SchwartzMap
open SevenEighths InverseMoment CanonicalCubeSeparation
open AngularRankData AngularRankSuccessor AngularEnergyData

theorem angular_rank_energy_exists_all_of_references (order : ℕ)
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32):
    ∀n:ℕ,∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→AngularRankEnergyExists order n L cstar cutoff eta K W :=by
  intro n
  induction n with
  | zero =>
      intro W lo hi hlo hhi hsW
      exact angular_rank_energy_exists_zero order L cstar cutoff eta hcut K W
  | succ n ih =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,hbox,hone⟩:=href lo hi hlo hhi
      exact angular_rank_energy_exists_succ_of_reference order n L cstar cutoff eta K hL hcstar hcut hcutL
        hcutc heta heta1 hetac hetad ih W lo hi hlo hhi hsW Vlog Alog hbox hone
        (fun window=>hthreshold eta heta hi Alog window)

theorem angular_canonical_energy_exists_of_references (order : ℕ)
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    AngularCanonicalEnergyExists order Mcap Fcap c eps (Fcap+1) K W :=by
  obtain ⟨n,cutoff,eta,hn,hpos,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,hmargin0,hmargin,hloss0,hloss⟩:=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  have he:=angular_rank_energy_exists_all_of_references order href hthreshold (Fcap+1) c cutoff eta K
    (by linarith) hc hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW
  exact angular_canonical_energy_of_rank order n (Fcap+1) c cutoff eta Mcap Fcap c eps K W
    hrow hcap hmargin hloss.le he

theorem angular_canonical_marked_energy_exists (order : ℕ)
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    AngularCanonicalEnergyExists order Mcap Fcap c eps (Fcap+1) K W :=
  angular_canonical_energy_exists_of_references order actual_rank_reference_cutoffs actual_rank_reference_thresholds
    Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW

#check @angular_canonical_marked_energy_exists
#print AngularCanonicalEnergyExists
#print axioms angular_canonical_marked_energy_exists
end
end OAI.CubicEisenstein.AngularEnergyExistence
