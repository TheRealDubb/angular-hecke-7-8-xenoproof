import AngularPhysicalZeroGrowthOriginal
import AngularPhysicalNaturalHighReserve
import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthContourBounded
noncomputable section
set_option maxHeartbeats 600000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.NaturalZeroGrowth
open Dyadic ConcreteTraceCRT QuadraticInitialBound EnergyState EnergyBands ReferenceState
open PlainRows
open NaturalRows CommonMask InductionEnergy RelativePrime NaturalReference
open CenteredMomentEnergyReferenceState (effectiveRadial)
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentEnergyBands (length length_nonneg)
open CenteredMomentEnergyReferenceChild (independentProfiles)
open CenteredMomentEnergyReferenceChildProfiles (reflectionProfiles)
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
open CenteredMomentEnergyReferenceLowControl (reflected_child_control)
open CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => ActualEisensteinCubic.O
variable {angularOrder:ℕ}
open CenteredMomentNaturalRowSource (fixedConductorFactor)
open CenteredMomentEnergyReferenceReflection (conductorFactor_pos)
open CenteredMomentEnergyReferenceState (radialEnergy_effective)
open CenteredMomentEnergyReferenceProfileBudget (reference_envelopes)
open CenteredMomentOriginalRadialComparison (finite_weighted)
open RadialSummability
open CenteredMomentEnergyReferenceScalarBounds (log_interval)
theorem ledger_bound (Mcap Bmask bΦ L d loss defect xi saving ε:ℝ)
    (_hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+1)+loss+defect+xi≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+L≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→∀s:NaturalState angularOrder Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBp:0<B:=by dsimp [B];positivity
  refine ⟨A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=NaturalReference.log_interval Z L d hZ hL hd
  have hm:max 1 s.radial.scale≤Z^s.width:=by
    apply max_le (Real.one_le_rpow hZ s.width_nonneg)
    rw [s.scale_eq]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    exact le_add_of_nonneg_right s.character_nonneg
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+loss+defect+xi)):=by gcongr
      _=A^d*B*Z^(s.width+(d*(Bmask+Mcap+1)+loss+defect+xi)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+loss+defect+xi)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herr:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
        Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+L)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add hreflect herr
    _=_:=by ring

private lemma ledger_loss_mono (Z d ell A B P w:ℝ)(hZ:1≤Z)(hd:0≤d)(hell:0≤ell)
    (hA:0≤A)(hB:0≤B)(hP:0≤P):
    P*(A*Z^(w+ell+d+d)+B)≤Z^ell*(P*(A*Z^(w+d+d+d)+B)):=by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:1≤Z^ell:=Real.one_le_rpow hZ hell
  have hm:Z^(w+ell+d+d)≤Z^ell*Z^(w+d+d+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _≤P*(A*(Z^ell*Z^(w+d+d+d))+Z^ell*B):=by
      apply mul_le_mul_of_nonneg_left _ hP
      exact add_le_add (mul_le_mul_of_nonneg_left hm hA)
        (le_mul_of_one_le_left hB hp)
    _=_:=by ring

theorem bounded_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧ Loriginal≤L ∧
      Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState angularOrder Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=min 1 (ε/(8*(Bmask+Mcap+4)))
  let L:=max Loriginal (Mcap+Bmask+2*d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=lt_min (by norm_num) (by positivity)
  have hd1:d≤1:=min_le_left _ _
  have hdε:d*(Bmask+Mcap+4)≤ε/8:=by
    have hh: d≤ε/(8*(Bmask+Mcap+4)):=min_le_right _ _
    have he: d*(8*(Bmask+Mcap+4))≤ε:=
      (le_div_iff₀ (by positivity)).mp hh
    linarith
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]
  have hs:0<saving:=by dsimp [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by linarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=ledger_bound
    Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  refine ⟨d,L,saving,C,hd,hd1,hL,hs,hC,rfl,?_,?_,hbound⟩
  · dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+2*d)]
  · dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+2*d)]

theorem zero_from_growth_additional_loss_bounded (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ Loriginal≤L ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧
      L≤max Loriginal (Mcap+Bmask+2)+1 ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(ell:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ell→0≤K→
        ZeroGrowthAt angularOrder Q a b bΦ Bmask L Mcap ell Z degree S K→
        ZeroAt angularOrder Q a b bΦ Bmask Loriginal Mcap (ell+ε) Z J U (C*(K+1)):=by
  obtain ⟨d,L,saving,Cledger,hd,hd1,hL,hsaving,hCledger,hLexact,hLoriginal,hroom,hledger⟩:=
    bounded_growth_reserve
      ε Mcap Bmask bΦ Loriginal hε hM hB
  refine ⟨d,L,hd,hd1,hL,hLoriginal,hLexact,?_,?_⟩
  · rw [hLexact]
    gcongr
    linarith only [hd1]
  intro S
  obtain ⟨J,U,Csource,hCsource,hsource⟩:=
    original_from_growth
      a b bΦ d d d saving L ha hlo hhi hbΦ hd hd hd S
  refine ⟨J,U,Csource*Cledger,mul_pos hCsource hCledger,?_⟩
  filter_upwards [hsource] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ell Q degree K hell hK hgrowth s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:Z^Loriginal≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hLoriginal
  have hh:=hZ.2 Bmask L Mcap ell Q degree K hK hgrowth hB hroom
    (by linarith) s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale)
  let Rcap:=max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)
  let A:=Rcap^d*(1+2*(L*Real.log Z))
  let B:=Rcap^(2*d)*Z^(-2*saving)*max 1 s.radial.scale*Z^L
  let P:=(s.puncture.radical.absNorm:ℝ)^d
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hA:0≤A:=by dsimp [A,Rcap];positivity
  have hBb:0≤B:=by dsimp [B,Rcap];positivity
  have hP:0≤P:=by dsimp [P];positivity
  have hb:=ledger_loss_mono Z d ell A B P s.width hZ.1.le hd.le hell hA hBb hP
  have hl:=mul_le_mul_of_nonneg_left (hledger Z hZ.1.le s hs) (Real.rpow_nonneg hz.le ell)
  have htotal:P*(A*Z^(s.width+ell+d+d)+B)≤Cledger*Z^(s.width+(ell+ε)):=by
    apply hb.trans
    calc
      _≤Z^ell*(Cledger*Z^(s.width+ε)):=hl
      _=Cledger*(Z^ell*Z^(s.width+ε)):=by ring
      _=Cledger*Z^(s.width+(ell+ε)):=by rw [←Real.rpow_add hz];congr 2;ring
  have hfront:0≤Csource*(K+1)*diagonalControl s.radial.profile*
      (p.control U)^2*(1+|t|)^J:=by
    have hd:=diagonalControl_nonneg s.radial.profile
    positivity
  calc
    _≤Csource*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*(1+|t|)^J*
        (Cledger*Z^(s.width+(ell+ε))):=by
      apply hh.trans
      convert mul_le_mul_of_nonneg_left htotal hfront using 1 ; dsimp only [P,A,B,Rcap] ; ring
    _=_:=by rw [Real.norm_eq_abs];ring


end OAI.SevenEighths.Angular.NaturalZeroGrowth

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.ledger_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.ledger_bound

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.bounded_growth_reserve
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.bounded_growth_reserve

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.zero_from_growth_additional_loss_bounded
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.zero_from_growth_additional_loss_bounded
