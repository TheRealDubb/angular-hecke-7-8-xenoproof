import AngularPhysicalNaturalSignedAnchor
import AngularPhysicalNaturalLowBands
import OAI.NumberTheory.DirichletL.Energy.LowBandEmpty
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.NaturalSignedAnchor
open EnergyState EnergyBands RelativePrime QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional NaturalReference InductionEnergy PlainRows
open CenteredMomentEnergyBands (length)
local notation "O" => ActualEisensteinCubic.O
def SignedZeroLowAt (n : ℕ) (Ω : AngularCharacter) (Q : Ideal O)
    (a b bΦ Bmask L M ε Z : ℝ) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState n Z Bmask bΦ, s.character.k = Ω.k →
    s.fixedModulus = internalQ Q Ω → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    X₁ ≤ Z^L → X₂ ≤ Z^L →
    length Z X₁+length Z X₂≤5*s.width/6 →
    s.plainEnergy p t X₁ X₂ ≤ C * diagonalControl s.radial.profile *
      (p.control S)^2 * (1+‖t‖)^degree * Z^(s.width+ε)

theorem zeroLowAt_of_signed_pair {n : ℕ} (Ω : AngularCharacter)
    (hΩ : Ω.k.natAbs = n) (Q : Ideal O)
    (a b bΦ Bmask L M ε Z : ℝ) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (Cplus Cminus : ℝ)
    (hp : SignedZeroLowAt n Ω Q a b bΦ Bmask L M ε Z degree S Cplus)
    (hm : SignedZeroLowAt n Ω.conjugate Q a b bΦ Bmask L M ε Z degree S Cminus) :
    ZeroLowAt n (internalQ Q Ω) a b bΦ Bmask L M ε Z degree S (max Cplus Cminus) := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  have hd := diagonalControl_nonneg s.radial.profile
  have hZ : 0 ≤ Z := zero_le_one.trans s.base_ge_one
  rcases parent_has_one_of_two_types Ω hΩ s with hk | hk
  · apply (hp s hk hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall).trans
    gcongr <;> first | exact le_max_left Cplus Cminus | positivity
  · apply (hm s hk hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall).trans
    gcongr <;> first | exact le_max_right Cplus Cminus | positivity


variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (angularOrder:ℕ)
omit [Fintype α] [DecidableEq α] in
theorem positive_low_signed_zero
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:AngularCharacter)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:PositiveLowAt (α:=α) M H hH angularOrder Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C):
    SignedZeroLowAt angularOrder η₀ Q a b bΦ Bmask L Mcap ε Z degree S C:=by
  intro s htype hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  let T:Finset α:=∅
  let θ:T→RayQuotient.Characters M H:=fun i=>False.elim (Finset.notMem_empty _ i.property)
  let w:T→ℝ:=fun _=>0
  have hcap:length Z X₁+length Z X₂+6*κ*(∑i:T,w i)≤s.width:=by
    simp only [T,w,Finset.sum_const_zero,mul_zero,add_zero]
    linarith [s.width_nonneg]
  have hl:length Z X₁+length Z X₂+(∑i:T,w i)≤5*s.width/6:=by
    simpa only [w,Finset.sum_const_zero,add_zero] using hsmall
  have hh:=h T θ w w w t 0 (fun _=>le_rfl)
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property)) le_rfl
    (fun _=>by simp [w]) s htype hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hl
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>(rayRelativeCharacter M H hH η₀ (θ i)).idealHom I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (w i) (w i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [T,energy,positiveSlotRow,NaturalState.plainEnergy,
      PlainZeroEnergy.zeroEnergy,PlainZeroEnergy.zeroRow,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid] at hh
  simpa only [add_zero,Real.norm_eq_abs] using hh


end OAI.SevenEighths.Angular.NaturalSignedAnchor

#print axioms OAI.SevenEighths.Angular.NaturalSignedAnchor.zeroLowAt_of_signed_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalSignedAnchor.zeroLowAt_of_signed_pair

#print axioms OAI.SevenEighths.Angular.NaturalSignedAnchor.positive_low_signed_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalSignedAnchor.positive_low_signed_zero
