import AngularPhysicalNaturalTerminalMoments
import AngularPhysicalDetectorPlainIdentity
import AngularPhysicalDetectorMarkedHeight
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorInitial
open EnergyState EnergyBands RelativePrime PlainRows NaturalRows InductionEnergy
open QuadraticInitialBound CenteredMomentFiniteProfileExceptional ConcretePrimeRowBridge
open CommonMask OAI.SevenEighths.Angular.Dyadic
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
open CenteredMomentDetectorDictionary
open CenteredMomentDetectorEnergyInitialState (detectorProfiles)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorDyadicProfiles (positiveAnnular)
open ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

-- Actual marked fourth moments at the original finite incumbent capacity.
-- No angular zero-free theorem or lower bound on beta_finite is assumed.
-- The common mesh and height degree still precede the target anchor/conductor.
theorem incumbent_relative_anchor_moment
    (n:ℕ) (W:ℝ→ℂ) (aslot bslot lo hi bΦ δ ε:ℝ)
    (haslot:0<aslot) (hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W) (hbslot:0≤bslot) (hbΦ:2≤bΦ)
    (hδ:0<δ) (hδhi:δ≤1) (hε:0<ε)
    (Φ:𝓢(ℝ,ℂ)) (hsΦ:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hpΦ:∀x,0≤(Φ x).re) (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    :
    ∃J:ℕ,∃S:Finset (ℕ×ℕ),∀Ω:AngularCharacter,Ω.k.natAbs=n→
    ∀Q:Ideal O,Q≤M→internalQ Q Ω≠0→internalQ Q Ω≠⊤→
      internalQ Q Ω≤Ideal.span {(72:O)}→
    ∀η:AngularCharacter,η.k=Ω.k→
    ∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,1<U ∧
    ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
      (∀i,0≤w i)→(∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 ε)→
      (∀i,lo≤σ i)→(∀i,σ i≤hi)→0≤height→(∀i,|v i|≤height)→
    ∀p:Profiles (1/4) (9/4),∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤U→X₂≤U→
      length U X₁+length U X₂+6*(3/4:ℝ)*(∑i,w i)≤1+δ→
    ∀rows:Finset O,(∀z∈rows,initialKeep η (internalQ Q Ω) z)→
      (∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤U)→
    (∑z∈rows,‖positiveSlotRow η fixedBadMask 1 z (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (U^(w i)))
      (fun i I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
        HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I)
      (fun i=>U^(w i)) t X₁ X₂‖^2)≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^J*U^(1+δ+ε) := by
  obtain ⟨J,S,ht⟩:=NaturalWidth.terminal_actual_bands (α:=α) M H hH n
    W aslot bslot (1/4) (9/4) bΦ 0 1 lo hi 2 (3/4) ε haslot hWs hW hbslot
    (by norm_num) (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num) (by norm_num) hε
  have hmesh := PhysicalDetectorUniform.commonMesh_le 2 0 1 (3/4) ε
    (by norm_num) (by norm_num) hε (by norm_num) (by norm_num)
  refine ⟨J,S,?_⟩
  intro Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  have hn:η.k.natAbs=n := (congrArg Int.natAbs hk).trans hΩ
  obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=ht Ω hΩ Q hQM hQ0 hQt hQ72
  have hmod:∀ᶠU:ℝ in atTop,(η.modulus.absNorm:ℝ)≤U^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [hbound,hmod] with U hU hη
  refine ⟨hU.1,?_⟩
  intro T θ w σ v t height hw hwmesh hσlo hσhi hh hv p X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity
    rows hkeep hrows
  let s:=initialState n η hn (internalQ Q Ω) Φ bΦ U δ hU.1.le hδ.le hsΦ hpΦ hη
  have hs:s.width≤2 := by change 1+δ≤2; linarith
  have hb:=hU.2.2 T θ w σ v t height hw (fun i=>(hwmesh i).trans hmesh) hσlo hσhi hh hv
    s hk rfl hs p X₁ X₂ hX₁ hX₂ (by simpa using hLX₁) (by simpa using hLX₂) hcapacity
  have hf:=finite_physical_le_energy η (internalQ Q Ω) Φ U (zero_lt_one.trans hU.1)
    hpΦ hone (p.profile 0) (p.profile 1) (9/4) (9/4) X₁ X₂
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun i=>primePool M H bslot (U^(w i)))
    (fun i I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
      HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I)
    (fun i=>U^(w i)) t rows hkeep hrows
  exact hf.trans hb


theorem incumbent_relative_detector_marked_profiles
    (n:ℕ) (W:ℝ→ℂ) (aslot bslot lo hi bΦ δ ε:ℝ)
    (haslot:0<aslot) (hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W) (hbslot:0≤bslot) (hbΦ:2≤bΦ)
    (hδ:0<δ) (hδhi:δ≤1) (hε:0<ε)
    (Φ:𝓢(ℝ,ℂ)) (hsΦ:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hpΦ:∀x,0≤(Φ x).re) (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    :
    ∃J:ℕ,∃S:Finset (ℕ×ℕ),∀Ω:AngularCharacter,Ω.k.natAbs=n→
    ∀Q:Ideal O,Q≤M→internalQ Q Ω≠0→internalQ Q Ω≠⊤→
      internalQ Q Ω≤Ideal.span {(72:O)}→
    ∀η:AngularCharacter,η.k=Ω.k→
    ∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,1<U ∧
    ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(height:ℝ),
      (∀i,0≤w i)→(∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 ε)→
      (∀i,lo≤σ i)→(∀i,σ i≤hi)→0≤height→(∀i,|v i|≤height)→
    ∀reverse:Bool,∀j k:ℕ,∀s freq X:ℝ,0<X→X≤U→
      2*length U X+6*(3/4:ℝ)*(∑i,w i)≤1+δ→
    ∀rows:Finset O,(∀z∈rows,initialKeep η (internalQ Q Ω) z)→
      (∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤U)→
    (∑z∈rows,‖polynomial
        (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[j]) positiveAnnular) X s freq*
      polynomial (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[k]) positiveAnnular) X s freq*
      ∏i,naturalSlot (naturalCharacter η z) (primePool M H bslot (U^(w i)))
        (fun I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I) (U^(w i))‖^2)≤
      C*diagonalControl Φ*((detectorProfiles reverse j k s freq).control S)^2*
        (1+height)^J*U^(1+δ+ε) := by
  obtain ⟨J,S,hm⟩:=incumbent_relative_anchor_moment (α:=α) M H hH n W aslot bslot lo hi bΦ δ ε
    haslot hWs hW hbslot hbΦ hδ hδhi hε Φ hsΦ hpΦ hone
  refine ⟨J,S,?_⟩
  intro Ω hn Q hQM hQ0 hQt hQ72 η hk
  obtain ⟨C,hC,hbound⟩:=hm Ω hn Q hQM hQ0 hQt hQ72 η hk
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro T θ w σ v height hw hwm hlo hhi hh hv reverse j k s freq X hX hXU hcap rows hkeep hrows
  have he:=hU.2 T θ w σ v 0 height hw hwm hlo hhi hh hv
    (detectorProfiles reverse j k s freq) X X hX hX hXU hXU (by linarith) rows hkeep hrows
  have hnorm (z:O) (hz:z∈rows):
      ‖positiveSlotRow η CenteredMomentSecondHeightFamily.fixedBadMask 1 z
        ((detectorProfiles reverse j k s freq).profile 0)
        ((detectorProfiles reverse j k s freq).profile 1)
        (fun i=>primePool M H bslot (U^(w i)))
        (fun i I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I)
        (fun i=>U^(w i)) 0 X X‖=
      ‖polynomial (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[j]) positiveAnnular) X s freq*
        polynomial (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[k]) positiveAnnular) X s freq*
        ∏i,naturalSlot (naturalCharacter η z) (primePool M H bslot (U^(w i)))
          (fun I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
            HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I) (U^(w i))‖ := by
    rw [natural_positive_zero (naturalRow η z (hkeep z hz).1) _ _ _ _ _
      (fun i=>Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _) X X hX hX]
    rw [←naturalCharacter_eq η z (hkeep z hz).1]
    simp only [detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
    norm_num only
    simp only [ite_false,norm_mul,detector_profile_norm _ reverse j X s freq hX,
      detector_profile_norm _ reverse k X s freq hX]
  have heq:=Finset.sum_congr rfl (fun z hz=>congrArg (fun x:ℝ=>x^2) (hnorm z hz))
  rw [heq] at he
  simpa only [abs_zero,add_zero] using he


theorem incumbent_relative_fixed_energy
    (n:ℕ) (W:ℝ→ℂ) (aslot bslot lo hi bΦ δ ε:ℝ)
    (haslot:0<aslot) (hWs:Function.support W⊆Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W) (hbslot:0≤bslot) (hbΦ:2≤bΦ)
    (hδ:0<δ) (hδhi:δ≤1) (hε:0<ε)
    (Φ:𝓢(ℝ,ℂ)) (hsΦ:Function.support (Φ:ℝ→ℂ)⊆Iic bΦ)
    (hpΦ:∀x,0≤(Φ x).re) (hone:∀x∈Icc (0:ℝ) 1,Φ x=1)
    :
    ∃J:ℕ,∀Ω:AngularCharacter,Ω.k.natAbs=n→
    ∀Q:Ideal O,Q≤M→internalQ Q Ω≠0→internalQ Q Ω≠⊤→
      internalQ Q Ω≤Ideal.span {(72:O)}→
    ∀η:AngularCharacter,η.k=Ω.k→
    ∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,1<U ∧
    ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(height:ℝ),
      (∀i,0≤w i)→(∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 ε)→
      (∀i,lo≤σ i)→(∀i,σ i≤hi)→0≤height→(∀i,|v i|≤height)→
    ∀reverse:Bool,∀j k:ℕ,j+k≤2→∀s∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
    ∀X:ℝ,0<X→X≤U→2*length U X+6*(3/4:ℝ)*(∑i,w i)≤1+δ→
    ∀rows:Finset O,(∀z∈rows,initialKeep η (internalQ Q Ω) z)→
      (∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤U)→
    (∑z∈rows,‖polynomial
        (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[j]) positiveAnnular) X s freq*
      polynomial (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[k]) positiveAnnular) X s freq*
      ∏i,naturalSlot (naturalCharacter η z) (primePool M H bslot (U^(w i)))
        (fun I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (v i) I) (U^(w i))‖^2)≤
      C*(1+height)^J*U^(1+δ+ε) := by
  obtain ⟨J,S,hm⟩:=incumbent_relative_detector_marked_profiles (α:=α) M H hH n W
    aslot bslot lo hi bΦ δ ε haslot hWs hW hbslot hbΦ hδ hδhi hε Φ hsΦ hpΦ hone
  obtain ⟨Jh,Ch,hCh,hprofile⟩:=CenteredMomentDetectorPlainProfileControl.source_height_factor S
  refine ⟨Jh+J,?_⟩
  intro Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  obtain ⟨C,hC,hbound⟩:=hm Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  let C₀:ℝ:=C*(1+diagonalControl Φ)*Ch
  have hd:0≤diagonalControl Φ:=diagonalControl_nonneg _
  have hC₀:0<C₀:=by dsimp [C₀]; positivity
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro T θ w σ v height hw hwm hlo hhi hh hv reverse j k hjk s hs freq hf
    X hX hXU hcap rows hkeep hrows
  have hUp:0<U:=zero_lt_one.trans hU.1
  have hb:=hU.2 T θ w σ v height hw hwm hlo hhi hh hv reverse j k s freq X hX hXU
    hcap rows hkeep hrows
  have hp:=hprofile J reverse j k hjk s hs height freq hh (abs_le.mpr hf)
  simp only [abs_zero,add_zero] at hp
  apply hb.trans
  calc
    _=(C*diagonalControl Φ)*
      (((detectorProfiles reverse j k s freq).control S)^2*(1+height)^J)*U^(1+δ+ε) := by ring
    _≤(C*(1+diagonalControl Φ))*(Ch*(1+height)^(Jh+J))*U^(1+δ+ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) hp
        (by positivity) (by positivity)
    _=C₀*(1+height)^(Jh+J)*U^(1+δ+ε) := by dsimp [C₀]; ring


theorem incumbent_row_height_plain_energy
    (n:ℕ) (W:ℝ→ℂ) (aslot bslot lo hi bΦ δ ε:ℝ)
    (haslot:0<aslot) (hWs:Function.support W⊆Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W) (hbslot:0≤bslot) (hbΦ:2≤bΦ)
    (hδ:0<δ) (hδhi:δ≤1) (hε:0<ε)
    (Φ:𝓢(ℝ,ℂ)) (hsΦ:Function.support (Φ:ℝ→ℂ)⊆Iic bΦ)
    (hpΦ:∀x,0≤(Φ x).re) (hone:∀x∈Icc (0:ℝ) 1,Φ x=1)
    :
    ∃J:ℕ,∀Ω:AngularCharacter,Ω.k.natAbs=n→
    ∀Q:Ideal O,Q≤M→internalQ Q Ω≠0→internalQ Q Ω≠⊤→
      internalQ Q Ω≤Ideal.span {(72:O)}→
    ∀η:AngularCharacter,η.k=Ω.k→
    ∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,1<U ∧
    ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(height:ℝ),
      (∀i,0≤w i)→(∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 ε)→
      (∀i,lo≤σ i)→(∀i,σ i≤hi)→0≤height→(∀i,|v i|≤height)→
    ∀reverse:Bool,∀j k:ℕ,j+k≤2→∀s∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
    ∀X:ℝ,0<X→X≤U→2*length U X+6*(3/4:ℝ)*(∑i,w i)≤1+δ→
    ∀rows:Finset O,(∀z∈rows,initialKeep η (internalQ Q Ω) z)→
      (∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤U)→
    ∀choice:O→ℝ,(∀z∈rows,|choice z|≤height)→
    (∑z∈rows,‖polynomial
        (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[j]) positiveAnnular) X s freq*
      polynomial (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
        false ((logProfile^[k]) positiveAnnular) X s freq*
      ∏i,naturalSlot (naturalCharacter η z) (primePool M H bslot (U^(w i)))
        (fun I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (choice z+v i) I) (U^(w i))‖^2)≤
      C*(1+height)^J*U^(1+δ+ε) := by
  let N:=Fintype.card α
  have hn (node:Fin (N+1)):=incumbent_relative_fixed_energy (α:=α) M H hH n
    (PhysicalDetectorMarkedHeight.commonProfile W node.val) aslot bslot lo hi bΦ δ ε haslot
    ((PhysicalDetectorMarkedHeight.commonProfile_support W node.val).trans hWs)
    (PhysicalDetectorMarkedHeight.commonProfile_smooth W aslot bslot haslot hWs hW node.val)
    hbslot hbΦ hδ hδhi hε Φ hsΦ hpΦ hone
  choose degree hn using hn
  let J:=∑node,degree node
  let cost:=PhysicalDetectorMarkedHeight.commonProfileCost N
  have hcost:0<cost:=zero_lt_one.trans_le (PhysicalDetectorMarkedHeight.commonProfileCost_ge_one N)
  refine ⟨J+1,?_⟩
  intro Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  choose C hC hb using fun node=>hn node Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  let Csum:=∑node,C node
  have hne:(Finset.univ:Finset (Fin (N+1))).Nonempty:=⟨0,Finset.mem_univ _⟩
  have hCs:0<Csum:=Finset.sum_pos (fun node _=>hC node) hne
  have hall:∀ᶠ U:ℝ in atTop,∀node,_:=eventually_all.mpr hb
  refine ⟨4*cost*Csum*2^J,by positivity,?_⟩
  filter_upwards [hall] with U hall
  refine ⟨(hall 0).1,?_⟩
  intro T θ w σ v height hw hwm hlo hhi hh hv reverse j k hjk s hs freq hf
    X hX hXU hcap rows hkeep hrows choice hchoice
  have hUp:0<U:=zero_lt_one.trans (hall 0).1
  let factor:=fun z=>polynomial
      (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
      false ((logProfile^[j]) positiveAnnular) X s freq*
    polynomial (if reverse then (naturalCharacter η z).conjugate else naturalCharacter η z)
      false ((logProfile^[k]) positiveAnnular) X s freq
  let E:=Csum*(1+2*height)^J*U^(1+δ+ε)
  have hE:0≤E:=by dsimp [E]; positivity
  have hmoment (node:Fin (N+1)) (t:ℝ) (ht:t∈Icc (-height) height):
      (∑z∈rows,‖factor z*∏i,naturalSlot (naturalCharacter η z)
        (primePool M H bslot (U^(w i)))
        (fun I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight (PhysicalDetectorMarkedHeight.commonProfile W node.val)
            (U^(w i)) (σ i) (t+v i) I) (U^(w i))‖^2)≤E := by
    have he:=(hall node).2 T θ w σ (fun i=>t+v i) (2*height) hw hwm hlo hhi
      (by positivity) (fun i=>(abs_add_le t (v i)).trans (by linarith [abs_le.mpr ht,hv i]))
      reverse j k hjk s hs freq ⟨by linarith [hf.1],by linarith [hf.2]⟩
      X hX hXU hcap rows hkeep hrows
    apply he.trans
    have hc:C node≤Csum:=Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ node)
    have hd:degree node≤J:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ node)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
    exact mul_le_mul hc (pow_le_pow_right₀ (by linarith) hd) (by positivity) hCs.le
  have hcard:(Finset.univ:Finset T).card≤N:=by
    simpa only [Finset.card_univ,Fintype.card_coe] using Finset.card_le_univ T
  have he:=PhysicalDetectorMarkedHeight.naturalSlot_rowwise_energy rows (Finset.univ:Finset T)
    N hcard (fun z=>naturalCharacter η z) (fun i=>primePool M H bslot (U^(w i)))
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1.ne_zero)
    (fun i I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I) W
    (fun i=>U^(w i)) σ v (fun i _=>Real.rpow_pos_of_pos hUp _) factor
    (-height) height E (by linarith) hE choice (fun z hz=>abs_le.mp (hchoice z hz)) hmoment
  apply he.trans
  have hpow:(1+2*height)^J≤2^J*(1+height)^J:=by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  change (1+2*(height- -height))*cost*(Csum*(1+2*height)^J*U^(1+δ+ε))≤_
  calc
    _≤(4*(1+height))*cost*(Csum*(2^J*(1+height)^J)*U^(1+δ+ε)) := by
      gcongr
      linarith
    _=_ := by rw [pow_succ]; ring

end OAI.SevenEighths.Angular.PhysicalDetectorInitial

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_relative_anchor_moment
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_relative_anchor_moment

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_relative_detector_marked_profiles
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_relative_detector_marked_profiles

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_relative_fixed_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_relative_fixed_energy

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_row_height_plain_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.incumbent_row_height_plain_energy
