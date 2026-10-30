import AngularPhysicalNaturalStageEntry
import AngularPhysicalNaturalSignedAnchor
import AngularPhysicalNaturalSourceInput
import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthSource
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace OAI.SevenEighths.Angular.NaturalZeroGrowth
open PlainRows PlainRows.CommonRows PlainRows.FirstPhysical
open EnergyState EnergyBands RelativePrime NaturalSignedAnchor
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBands (length)
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentEnergyReferenceState
  (comparisonFirst comparisonSecond comparison_positive comparison_same_product)
local notation "O"=>ActualEisensteinCubic.O
variable {angularOrder:ℕ}
local instance successorZeroPhysicalSignDecEq : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _
def balancedInput {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):Input (Fin 0):=
  naturalInput s p ha (fun _=>∅) (by simp) (fun _=>s.character) (fun _=>0)
    (fun _=>1) (fun _=>1) (by simp) (by simp) 1 1 (by norm_num)
    (by simp) (by simp) t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂ (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

lemma balanced_volume {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(p:Profiles a b)
    (ha:0<a)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    PlainRows.CommonRows.volume (balancedInput s p ha t X₁ X₂ hX₁ hX₂)=X₁*X₂:=by
  simp only [PlainRows.CommonRows.volume,
    balancedInput,naturalInput,completeInput,naturalData,Finset.univ_eq_empty,Finset.prod_empty,mul_one]

def PhysicalGrowthAt (angularOrder:ℕ) (Q:Ideal O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState angularOrder Z Bmask bΦ,s.fixedModulus=Q→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)

def SignedPhysicalGrowthAt (angularOrder:ℕ) (Ω:AngularCharacter) (Q:Ideal O)(a b bΦ Bmask L rho Mcap ξ e Z:ℝ)(ha:0<a)
    (Ψ:𝓢(ℝ,ℂ))(S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀s:NaturalState angularOrder Z Bmask bΦ,s.character.k=Ω.k→s.fixedModulus=internalQ Q Ω→ rho≤s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→5*s.width/6≤length Z X₁+length Z X₂→
    let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
    (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
      Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
    physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
      C*(p.control S)^2*(1+|t|)^J*Z^(max s.width (length Z X₁+length Z X₂)+e)


theorem physicalGrowthAt_of_signed_pair (Ω:AngularCharacter)
    (hΩ:Ω.k.natAbs=angularOrder) (Q:Ideal O)
    (a b bΦ Bmask L rho Mcap ξ e Z:ℝ) (ha:0<a)
    (Ψ:𝓢(ℝ,ℂ)) (S:Finset (ℕ×ℕ)) (J:ℕ) (Cp Cm:ℝ)
    (hp:SignedPhysicalGrowthAt angularOrder Ω Q a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J Cp)
    (hm:SignedPhysicalGrowthAt angularOrder Ω.conjugate Q a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J Cm):
    PhysicalGrowthAt angularOrder (internalQ Q Ω) a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J (max Cp Cm):=by
  intro s hQ hrho hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hhigh
  dsimp only
  intro hfour
  have hz:0≤Z:=zero_le_one.trans s.base_ge_one
  rcases parent_has_one_of_two_types Ω hΩ s with hk|hk
  · apply (hp s hk hQ hrho hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hhigh hfour).trans
    gcongr <;> first | exact le_max_left Cp Cm | positivity
  · apply (hm s hk hQ hrho hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hhigh hfour).trans
    gcongr <;> first | exact le_max_right Cp Cm | positivity

/-- Constants and thresholds may differ between the two fixed anchors.
The smoothing profile and seminorm data must already be common. -/
theorem eventual_physicalGrowthAt_of_signed_pair (Ω:AngularCharacter)
    (hΩ:Ω.k.natAbs=angularOrder) (Q:Ideal O)
    (a b bΦ Bmask L rho Mcap ξ e:ℝ) (ha:0<a)
    (Ψ:𝓢(ℝ,ℂ)) (S:Finset (ℕ×ℕ)) (J:ℕ)
    (hp:∃Cp:ℝ,0<Cp ∧ ∀ᶠZ:ℝ in atTop,
      SignedPhysicalGrowthAt angularOrder Ω Q a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J Cp)
    (hm:∃Cm:ℝ,0<Cm ∧ ∀ᶠZ:ℝ in atTop,
      SignedPhysicalGrowthAt angularOrder Ω.conjugate Q a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J Cm):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
      PhysicalGrowthAt angularOrder (internalQ Q Ω) a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J C:=by
  obtain ⟨Cp,hCp,hp⟩:=hp
  obtain ⟨Cm,hCm,hm⟩:=hm
  refine ⟨max Cp Cm,hCp.trans_le (le_max_left _ _),?_⟩
  filter_upwards [hp,hm] with Z hp hm
  exact physicalGrowthAt_of_signed_pair Ω hΩ Q a b bΦ Bmask L rho Mcap ξ e Z ha Ψ S J Cp Cm hp hm

end OAI.SevenEighths.Angular.NaturalZeroGrowth

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.balanced_volume
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.balanced_volume

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.physicalGrowthAt_of_signed_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.physicalGrowthAt_of_signed_pair

#print axioms OAI.SevenEighths.Angular.NaturalZeroGrowth.eventual_physicalGrowthAt_of_signed_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalZeroGrowth.eventual_physicalGrowthAt_of_signed_pair
