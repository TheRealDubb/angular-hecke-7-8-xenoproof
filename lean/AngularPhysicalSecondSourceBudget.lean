import AngularPhysicalFrozenDescent
import AngularPhysicalChildSourceVolume
import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.SecondSourcePower
open PlainRows PlainRows.CommonRows PlainRows.RadialEnergy ChildRows SecondFamily ChildState
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentSecondOriginalChildren (sourceRadial)
open CenteredMomentSecondPhysicalBlock (outerScalar)
open CenteredMomentSecondDyadicRowSupport (dyadicRows dyadicRows_subset dyadicRows_norm)
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg ballProfile_majorizes)
open CenteredMomentSecondHeightFamily (fixedBadMask)
open Filter
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance {κ:Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open PhysicalBlock CenteredMomentSourceLiveColumn

open SourceCapacity CenteredMomentCommonHeightEnvelope
open ConcretePrimeRowBridge
open PlainRows.SecondSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSecondBlockHarmonicMass CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedRatioScalar (retainedRatio)
open SecondNonexceptionalAggregate PhysicalBlock

open FiniteProfileExceptional CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open EisensteinSchwartzPoisson

open MeasureTheory UniqueFactorizationMonoid
open PlainRows.ChildInputs PlainRows.ChildSourceCaps
open CenteredMomentCommonProfile
open DetectorAmplitude (slotControl slotControl_nonneg)
open CommonExceptionalSource (frozenProfile frozenProfile_nonneg)
open FiniteProfileExceptionalPhysical (profileFactor profileFactor_nonneg)
open CenteredMomentFirstChildProfileControl (exceptionalConstant)
open CenteredMomentSecondChildPowerBudget (coefficients powers)
def mass (s : Input ι) : ℝ := ∏ i,s.M i

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤mass s :=
  Finset.one_le_prod₀ (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤mass s := zero_le_one.trans (mass_one s)

omit [DecidableEq ι] in
lemma slot_control_bound (s : Input ι) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) :
    slotControl s.toData≤(128*b)^Fintype.card ι*mass s^2 := by
  have hpoint (i : ι) : max 1 (128*max 0 (s.hi i)*s.M i)≤(128*b)*s.M i := by
    apply max_le
    · have hM:=s.M_ge_one i
      nlinarith
    · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (s.M_ge_one i))
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) ((s.upper_ge i).trans hu)) (by norm_num)
  have hp:=Finset.prod_le_prod₀ (fun i (_:i∈Finset.univ)=>by positivity)
    (fun i (_:i∈Finset.univ)=>hpoint i)
  calc
    slotControl s.toData=mass s*(∏i,max 1 (128*max 0 (s.hi i)*s.M i)):=rfl
    _≤mass s*(∏i,(128*b)*s.M i):=mul_le_mul_of_nonneg_left hp (mass_nonneg s)
    _=(128*b)^Fintype.card ι*mass s^2:=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      unfold mass
      ring

omit [DecidableEq ι] in
lemma profile_cost_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileCost s≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*A^2)*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have hm2:=pow_le_pow_left₀ (mass_nonneg s) hm 2
  have h:=mul_le_mul hm2 hp (by positivity) (sq_nonneg A)
  have h':=(mul_le_mul_of_nonneg_right h
    (show 0≤2*(max 1 s.b₁*max 1 s.b₂)*mass s^2 by positivity))
  convert h' using 1 <;> simp only [profileCost,PlainRows.Data.profileFactor,mass]; ring

omit [DecidableEq ι] in
lemma exceptional_slot_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    slotControl s.toData^2*frozenProfile s^2≤
      ((128*b)^N)^2*(b^N)^2*A^4*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have h128 : (1:ℝ)≤128*b := by linarith
  have hs : slotControl s.toData≤(128*b)^N*mass s^2 :=
    (slot_control_bound s b hb hu).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h128 hc) (sq_nonneg _))
  have hf : frozenProfile s≤mass s*b^N :=
    mul_le_mul_of_nonneg_left hp (mass_nonneg s)
  have h:=mul_le_mul (pow_le_pow_left₀ (slotControl_nonneg _) hs 2)
    (pow_le_pow_left₀ (frozenProfile_nonneg s) hf 2) (sq_nonneg _) (sq_nonneg _)
  calc
    _≤((128*b)^N*mass s^2)^2*(mass s*b^N)^2:=h
    _=((128*b)^N)^2*(b^N)^2*mass s^4*mass s^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg s) hm 4) (by positivity))
      (sq_nonneg _)

omit [DecidableEq ι] in
lemma exceptional_factor_bound {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K : ℝ)
    (hK : 0≤K) (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileFactor S s p J Q K≤exceptionalConstant N b J Q K*
      p.control S^2*(1+‖s.t‖)^(2*J)*A^4*mass s^2 := by
  have h:=exceptional_slot_bound s N b A hb hu hc hm
  let F:=K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*p.control S^2*(1+‖s.t‖)^(2*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hh:=mul_le_mul_of_nonneg_left h hF
  convert hh using 1 <;> simp only [profileFactor,exceptionalConstant,F] <;> ring

omit [DecidableEq ι] in
lemma endpoint_product (s : Input ι) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i) :
    0≤∏i,s.hi i ∧ (∏i,s.hi i)≤b^N := by
  refine ⟨Finset.prod_nonneg (fun i _=>hhi i),?_⟩
  calc
    _≤∏i:ι,b:=Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>(s.upper_ge i).trans hu)
    _=b^Fintype.card ι:=by simp
    _≤b^N:=pow_le_pow_right₀ hb hc

omit [DecidableEq ι] in
lemma main_cost (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) :
    profileCost s*sourceRadius s≤
      (2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)*
        PlainRows.CommonRows.volume s*mass s^2 := by
  have hg:=PlainRows.ChildSourceCaps.radius_le N b b₁ b₂ hb
    (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc hhi
    (fun i=>(s.upper_ge i).trans hu) hs₁ hs₂ hb₁ hb₂
  have hp:=profile_cost_bound s N b A hb hu hc hm
  have he : max 1 s.b₁*max 1 s.b₂≤b₁*b₂ :=
    mul_le_mul (max_le h₁ hb₁) (max_le h₂ hb₂) (by positivity) (by linarith)
  have hp' : profileCost s≤(2*(b₁*b₂)*b^N*A^2)*mass s^2 := by
    apply hp.trans
    gcongr
  have hh:=mul_le_mul hp' hg.2 hg.1 (by positivity)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma diagonal_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) (N : ℕ) (b whi ε : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (hhi : ∀i,0≤s.hi i) (hε : 0≤ε) :
    (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)≤
    (4*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
      (1+b^N*whi^2)^(1+ε))*mass s^2 := by
  have hp:=endpoint_product s N b hb hu hc hhi
  have hx : 1+(∏i,s.hi i)*whi*whi≤1+b^N*whi^2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 (sq_nonneg whi)]
  have hx0 : 0≤1+(∏i,s.hi i)*whi*whi := by nlinarith [mul_nonneg hp.1 (sq_nonneg whi)]
  have h:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx (by linarith : 0≤1+ε))
    (sq_nonneg (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s))
  convert h using 1 ; ring

omit [DecidableEq ι] in
lemma tail_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    plainControl s W₁ W₂^2=
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*mass s^2 := by
  unfold plainControl mass
  ring

def sourceCost {wlo whi : ℝ} (s : Input ι) (S : Finset (ℕ×ℕ))
    (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ)
    (a : Fin 4→ℝ) : ℝ :=
    a 0*profileCost s*sourceRadius s/seedNorm+
    a 1*profileFactor S s p J Q K*(PlainRows.CommonRows.volume s)^(1/3:ℝ)/seedNorm+
    a 2*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)*(PlainRows.CommonRows.volume s)^ε/seedNorm+
    a 3*plainControl s (p.profile 0) (p.profile 1)^2

omit [DecidableEq ι] in
theorem source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ) (hK : 0≤K) (hε : 0≤ε)
    (hs : 0≤seedNorm) (a : Fin 4→ℝ) (ha : ∀j,0≤a j) :
    sourceCost s S p J Q K ε seedNorm a ≤
      (∑j,coefficients N b b₁ b₂ A S p J Q K s.t ε seedNorm a j*
        (PlainRows.CommonRows.volume s)^(powers ε j))*mass s^2 := by
  unfold sourceCost
  have hv := (PlainRows.CommonRows.volume_pos s).le
  have hmain:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (main_cost s N b b₁ b₂ A hb h₁ h₂ hu hc hhi hs₁ hs₂ hb₁ hb₂ hm) (ha 0)) hs
  have hexc:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exceptional_factor_bound S p J Q K hK s N b A hb hu hc hm) (ha 1))
      (Real.rpow_nonneg hv (1/3:ℝ))) hs
  have hdiag:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (diagonal_cost s (p.profile 0) (p.profile 1) N b whi ε hb hu hc hhi hε) (ha 2))
      (Real.rpow_nonneg hv ε)) hs
  have htail:=congrArg (fun x:ℝ=>a 3*x) (tail_cost s (p.profile 0) (p.profile 1))
  have hh:=add_le_add (add_le_add (add_le_add hmain hexc) hdiag) (le_of_eq htail)
  convert hh using 1 <;>
    (try simp only [coefficients,powers,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.rpow_one,Real.rpow_zero]) <;> ring


end OAI.SevenEighths.Angular.SecondSourcePower

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.mass_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.mass_one

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.mass_nonneg
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.mass_nonneg

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.slot_control_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.slot_control_bound

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.profile_cost_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.profile_cost_bound

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.exceptional_slot_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.exceptional_slot_bound

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.exceptional_factor_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.exceptional_factor_bound

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.endpoint_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.endpoint_product

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.main_cost
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.main_cost

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.diagonal_cost
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.diagonal_cost

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.tail_cost
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.tail_cost

#print axioms OAI.SevenEighths.Angular.SecondSourcePower.source_rhs
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondSourcePower.source_rhs
