import AngularPhysicalNaturalCertifiedBand
import AngularPhysicalNaturalLowStage
import OAI.NumberTheory.DirichletL.Energy.CappedRequests
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
open NaturalStage NaturalReference
open NaturalSignedAnchor (zeroLowAt_of_signed_pair)
open CenteredMomentEnergyCappedRequests CenteredMomentEnergySourceCapSchedule
theorem actual_capped_low
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤bslot)
    (ha:0<a)(hb:0≤b)(hrad:2≤radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε)
    (k:ℕ)(hk:k<count Mcap ε)
    (hold:CertifiedBand (α:=α) M H hH angularOrder
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:AngularCharacter,η₀.k.natAbs=angularOrder→∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
        PositiveLowAt (α:=α) M H hH angularOrder W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt angularOrder (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C :=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Ag:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1))
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap ε)
  have hAg:0≤Ag:=by dsimp [Ag];positivity
  have hMp:0≤Mp:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε (k+1)
  have hMc:0≤Mc:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε k
  have hMpCap:Mp≤Mcap:=bandWidth_le Mcap Bs ε (k+1)
  have hMpAg:Mp≤Ag:=by dsimp [Ag];linarith
  have hLnext:0≤lengthAt Mcap Bmask L ε (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0≤Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hκ0:0≤κ:=by linarith
  have hbounds:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have hmesh:0≤fineMesh Mcap Bmask L κ ε:=hbounds.2.2.2.2.1.le
  have hr:0<reserve Mcap Bs ε:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs ε/4≤1:=by
    have hh:reserve Mcap Bs ε≤amplification ε/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask≤Bs:=
    readyBudget_le_schedule Mcap Bmask L ε Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤Mc:=parent_drop Mcap Bs ε hε k
  have hlength:2*max Lreq Mp+reserve Mcap Bs ε/4≤lengthAt Mcap Bmask L ε k:=
    previous_admits Mcap Bmask L ε Mp (reserve Mcap Bs ε/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap ε k hk
  obtain ⟨degree,S,hold⟩:=hold
  obtain ⟨U,J,hstage⟩:=actual_low_from_bands
    (α:=α) M H hH angularOrder W hW aslot bslot lo hi (lowerAt a b Mcap ε (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap ε ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L κ ε) κ ε k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hκ hε
    le_rfl hdrop degree S
  refine ⟨U,J,?_⟩
  intro η₀ hη Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,Cp,hCz,hCp,hOldP⟩:=hold η₀ hη Q hQM hQ0 hQt hQ72
  obtain ⟨_Czm,Cm,_hCzm,hCm,hOldM⟩:=hold η₀.conjugate (by simpa using hη) Q hQM hQ0 hQt hQ72
  obtain ⟨Csp,hCsp,hStageP⟩:=hstage η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Csm,hCsm,hStageM⟩:=hstage η₀.conjugate Q hQM hQ0 hQt hQ72
  let CpOut:=Csp*(Cz+Cp+1)
  let CmOut:=Csm*(Cz+Cm+1)
  refine ⟨max CpOut CmOut,(show 0<CpOut by dsimp [CpOut];positivity).trans_le (le_max_left _ _),?_⟩
  filter_upwards [hOldP,hOldM,hStageP,hStageM] with Z hOldP hOldM hsP hsM
  have hz:=hOldP.2.1
  have hp:=hOldP.2.2
  have hm:=hOldM.2.2
  rw [hsupport] at hz hp hm
  have hz':ZeroAt angularOrder (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) Mc (stageLoss Mcap Bs ε k) Z degree S Cz:=
    zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hOldP.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':PositiveAt (α:=α) M H hH angularOrder W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cp Cp hOldP.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  have hm':PositiveAt (α:=α) M H hH angularOrder W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀.conjugate Q degree S Cm:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀.conjugate Q degree degree S S Cm Cm hOldP.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCm.le le_rfl hm
  have hpNew:=hsP.2 (stageLoss Mcap Bs ε k) Cz Cp le_rfl hCz.le hCp.le hz' hp'
  have hmNew:=hsM.2 (stageLoss Mcap Bs ε k) Cz Cm le_rfl hCz.le hCm.le hz' hm'
  refine ⟨hsP.1,?_,?_⟩
  · exact NaturalBandTransport.positiveLowAt_transport (α:=α) M H hH W bslot
      _ _ _ _ _ _ _ _ _ _ κ Z _ _ _ _ _ _ _ η₀ Q J J U U CpOut (max CpOut CmOut)
      hsP.1.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) (by dsimp [CpOut];positivity) (le_max_left _ _) hpNew.1
  · exact zeroLowAt_of_signed_pair η₀ hη Q
      (lowerAt a b Mcap ε (k+1)) b radial Bmask Lreq Mp
      (physicalLoss Mcap Bs ε k) Z J U CpOut CmOut hpNew.2 hmNew.2

end OAI.SevenEighths.Angular.NaturalWidth

#print axioms OAI.SevenEighths.Angular.NaturalWidth.actual_capped_low
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.actual_capped_low
