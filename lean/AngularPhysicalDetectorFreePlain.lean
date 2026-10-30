import AngularPhysicalDetectorIncumbentPlain

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorJoint
open NaturalRows PlainRows CommonMask RelativePrime PhysicalDetectorInitial
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (FreeRow)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorDyadicProfiles (positiveAnnular)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

-- The actual plain source on exactly the free-row population used by the joint count.
theorem actual_free_plain_energy
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
    ∀rows:Finset FreeRow,(∀z∈rows,initialKeep η (internalQ Q Ω) z.val)→
      (∀z∈rows,((Ideal.span {z.val}).absNorm:ℝ)≤U)→
    ∀choice:FreeRow→ℝ,(∀z∈rows,|choice z|≤height)→
    (∑z∈rows,‖polynomial
        (if reverse then (naturalCharacter η z.val).conjugate else naturalCharacter η z.val)
        false ((logProfile^[j]) positiveAnnular) X s freq*
      polynomial (if reverse then (naturalCharacter η z.val).conjugate else naturalCharacter η z.val)
        false ((logProfile^[k]) positiveAnnular) X s freq*
      ∏i,naturalSlot (naturalCharacter η z.val) (primePool M H bslot (U^(w i)))
        (fun I=>(rayRelativeCharacter M H hH Ω (θ i)).idealHom I*
          HeckePrimeAnnular.annularWeight W (U^(w i)) (σ i) (choice z+v i) I) (U^(w i))‖^2)≤
      C*(1+height)^J*U^(1+δ+ε) := by
  obtain ⟨J,hm⟩ := incumbent_row_height_plain_energy (α:=α) M H hH n W
    aslot bslot lo hi bΦ δ ε haslot hWs hW hbslot hbΦ hδ hδhi hε Φ hsΦ hpΦ hone
  refine ⟨J,?_⟩
  intro Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  obtain ⟨C,hC,hbound⟩ := hm Ω hΩ Q hQM hQ0 hQt hQ72 η hk
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro T θ w σ v height hw hwm hlo hhi hh hv reverse j k hjk s hs freq hf
    X hX hXU hcap rows hkeep hrows choice hchoice
  let f : FreeRow→O := fun u=>u.val
  have hinj : Function.Injective f := Subtype.val_injective
  let choice' : O→ℝ := Function.extend f choice (fun _=>0)
  have hchoice' (u:FreeRow) : choice' (f u)=choice u := hinj.extend_apply choice (fun _=>0) u
  have hk' (z:O)(hz:z∈rows.image f) : initialKeep η (internalQ Q Ω) z := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact hkeep u hu
  have hn' (z:O)(hz:z∈rows.image f) : ((Ideal.span {z}).absNorm:ℝ)≤U := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact hrows u hu
  have hh' (z:O)(hz:z∈rows.image f) : |choice' z|≤height := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    rw [hchoice']
    exact hchoice u hu
  have he := hU.2 T θ w σ v height hw hwm hlo hhi hh hv reverse j k hjk s hs freq hf
    X hX hXU hcap (rows.image f) hk' hn' choice' hh'
  rw [Finset.sum_image (fun u _ v _ huv=>hinj huv)] at he
  simpa only [hchoice',f] using he

end OAI.SevenEighths.Angular.PhysicalDetectorJoint

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.actual_free_plain_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.actual_free_plain_energy
