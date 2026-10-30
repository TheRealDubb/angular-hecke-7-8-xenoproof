import AngularPhysicalNaturalReferenceRestoration
import OAI.NumberTheory.DirichletL.Energy.StageReserveBounded
noncomputable section
set_option maxHeartbeats 400000
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalReference
open Dyadic ConcreteTraceCRT QuadraticInitialBound EnergyState ReferenceState EnergyBands
open ConcretePrimeRowBridge
open NaturalRows CommonMask InductionEnergy RelativePrime
open EnergyAllocatedChildren
open CenteredMomentCommonMaskEnergy (heightCoefficient)
open CenteredMomentEnergyReferenceState (effectiveRadial)
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentEnergyBands (length length_nonneg)
open CenteredMomentEnergyReferenceChild (independentProfiles)
open CenteredMomentEnergyReferenceChildProfiles (reflectionProfiles)
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
open CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot (primePool)
local notation "O" => ActualEisensteinCubic.O
variable {angularOrder:ℕ}
open Filter
open PlainRows AllocatedNatural
open CenteredMomentNaturalRowSource (fixedConductorFactor support_prime)
open CenteredMomentCommonMaskEnergy (heightCoefficient_norm positive_height_phase_norm triple_sum)
open CenteredMomentCommonMaskExpansion (uniformMajorant uniformMajorant_nonneg)
open CenteredMomentEnergyReferenceState (radialEnergy_effective)
open CenteredMomentEnergyReferenceWeightedEnergy (radial_weighted_energy)
open RadialSummability
lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(d:ℝ)(hd:0≤d):
    (s.puncture.radical.absNorm:ℝ)^d≤Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤Mcap)(hd:0≤d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤Mcap:=s.width_nonneg.trans hs
  have hz:1≤Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma radial_scale {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ):
    max 1 s.radial.scale≤Z^s.width:=by
  rw [s.scale_eq]
  apply max_le (Real.one_le_rpow s.base_ge_one s.width_nonneg)
  apply Real.rpow_le_rpow_of_exponent_le s.base_ge_one
  exact le_add_of_nonneg_right s.character_nonneg

lemma physical_slot_product {α:Type*}[Fintype α](Z:ℝ)(hZ:1≤Z)(w:α→ℝ)(Mcap:ℝ)
    (hwidth:(∑i,w i)≤Mcap): (∏i,Z^(w i))≤Z^Mcap:=by
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ hwidth

lemma short_slot_mass {α:Type*}[Fintype α]{Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (Mcap:ℝ)(hs:s.width≤Mcap)(w:α→ℝ)(hwidth:(∑i,w i)≤Mcap):
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))≤Z^(s.width+5*Mcap/4):=by
  have hz:0<Z:=zero_lt_one.trans_le s.base_ge_one
  calc
    _≤Z^s.width*Z^(Mcap/4)*Z^Mcap:=by
      apply mul_le_mul (mul_le_mul (radial_scale s)
        (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (physical_slot_product Z s.base_ge_one w Mcap hwidth)
        (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg hz.le _)) (by positivity)
    _=Z^(s.width+5*Mcap/4):=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

lemma log_interval (Z L d:ℝ)(hZ:1≤Z)(hL:0≤L)(hd:0<d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

theorem ledger_bound (Mcap Bmask bΦ L d saving ε:ℝ)
    (hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+2)≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z → ∀s:NaturalState angularOrder Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBpos:0<B:=by dsimp only [B];positivity
  refine ⟨1+A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs α inst w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:=short_slot_mass s Mcap hs w hw
  have hdirect:(s.puncture.radical.absNorm:ℝ)^d*Z^(s.width+d)≤Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*Z^(s.width+d):=mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hz.le _)
      _=Z^(s.width+d*(Bmask+1)):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+d))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+d)):=by
        gcongr
      _=A^d*B*Z^(s.width+d*(Bmask+Mcap+2)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+d)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herrorTerm:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
        max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _=(s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          (max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))):=by ring
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by
        gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤Z^(s.width+ε)+A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add (add_le_add hdirect hreflect) herrorTerm
    _=_:=by ring

theorem exists_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀Z:ℝ,1≤Z → ∀s:NaturalState angularOrder Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let d:=ε/(4*(Bmask+Mcap+2))
  let xi:=rho/100
  let saving:=2*Mcap+Bmask*d+2*Mcap*d+1
  let L:=Mcap+Bmask+xi+1
  have hd:0<d:=by dsimp only [d];positivity
  have hxi:0<xi:=by dsimp only [xi];positivity
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hL:0≤L:=by dsimp only [L];positivity
  have hmain:d*(Bmask+Mcap+2)≤ε:=by
    dsimp only [d]
    have hp:0<Bmask+Mcap+2:=by positivity
    field_simp
    nlinarith
  have herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hledger⟩:=ledger_bound Mcap Bmask bΦ L d saving ε hM hB hL hd hmain herror
  exact ⟨d,xi,saving,L,C,hd,hxi,hsave,hC,le_rfl,by dsimp only [L];linarith,hledger⟩

theorem exists_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState angularOrder Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_reference_reserve (angularOrder:=angularOrder) rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hze:1≤Z^e:=Real.one_le_rpow hZ he
  have hp:Z^(s.width+e)≤Z^e*Z^(s.width+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  let A:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))
  let B:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hLp:0≤L:=by linarith
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hA:0≤A:=by dsimp [A];positivity
  have hB0:0≤B:=by dsimp [B];positivity
  have hb:B≤Z^e*B:=by nlinarith
  have hh:=add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hp hA)) hb
  have hrad:0≤(s.puncture.radical.absNorm:ℝ)^d:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh':=(mul_le_mul_of_nonneg_left hh hrad)
  have hend:=mul_le_mul_of_nonneg_left (hledger Z hZ s hwidth α w hw)
    (Real.rpow_nonneg hz.le e)
  calc
    _≤Z^e*((s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+d)+A*Z^(s.width+d)+B)):=by
      convert hh' using 1 ; dsimp [A,B] ; ring
    _≤Z^e*(C*Z^(s.width+ε)):=by
      exact hend
    _=C*Z^(s.width+e+ε):=by
      rw [mul_left_comm,←Real.rpow_add hz]
      congr 2
      ring

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState angularOrder Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_separated_reference_reserve (angularOrder:=angularOrder) rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,Mcap+Bmask+xi,C,hd,hxi,hs,hC,hxr,le_refl _,by linarith,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  apply le_trans _ (hledger e he Z hZ s hwidth α w hw)
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hLp:0≤Mcap+Bmask+xi:=by linarith
  gcongr


end OAI.SevenEighths.Angular.NaturalReference

#print axioms OAI.SevenEighths.Angular.NaturalReference.radical_power
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.radical_power

#print axioms OAI.SevenEighths.Angular.NaturalReference.conductor_power
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.conductor_power

#print axioms OAI.SevenEighths.Angular.NaturalReference.radial_scale
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.radial_scale

#print axioms OAI.SevenEighths.Angular.NaturalReference.physical_slot_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.physical_slot_product

#print axioms OAI.SevenEighths.Angular.NaturalReference.short_slot_mass
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.short_slot_mass

#print axioms OAI.SevenEighths.Angular.NaturalReference.log_interval
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.log_interval

#print axioms OAI.SevenEighths.Angular.NaturalReference.ledger_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.ledger_bound

#print axioms OAI.SevenEighths.Angular.NaturalReference.exists_reference_reserve
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.exists_reference_reserve

#print axioms OAI.SevenEighths.Angular.NaturalReference.exists_separated_reference_reserve
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.exists_separated_reference_reserve

#print axioms OAI.SevenEighths.Angular.NaturalReference.exists_bounded_separated_reference_reserve
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.exists_bounded_separated_reference_reserve
