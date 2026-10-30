import AngularPhysicalPositiveEnergyBands
import AngularPhysicalAllocatedRayMatches

/-!
The ZERO band ranges over both signed types. A fixed-anchor physical proof
only supplies its own signed type. The two-anchor repair below preserves the
actual fixed modulus and actual energy. It assumes the signed energy bounds;
it proves neither those bounds nor a complete successor.
-/
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.NaturalSignedAnchor
open EnergyState EnergyBands RelativePrime QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional
local notation "O" => ActualEisensteinCubic.O

def SignedZeroAt (n : ℕ) (Ω : AngularCharacter) (Q : Ideal O)
    (a b bΦ Bmask L M ε Z : ℝ) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState n Z Bmask bΦ, s.character.k = Ω.k →
    s.fixedModulus = internalQ Q Ω → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    X₁ ≤ Z^L → X₂ ≤ Z^L →
    s.plainEnergy p t X₁ X₂ ≤ C * diagonalControl s.radial.profile *
      (p.control S)^2 * (1+‖t‖)^degree * Z^(s.width+ε)

theorem conjugate_internalQ (Q : Ideal O) (Ω : AngularCharacter) :
    internalQ Q Ω.conjugate = internalQ Q Ω := rfl

theorem parent_has_one_of_two_types {n : ℕ} (Ω : AngularCharacter)
    (hΩ : Ω.k.natAbs = n) {Z Bmask bΦ : ℝ}
    (s : NaturalState n Z Bmask bΦ) :
    s.character.k = Ω.k ∨ s.character.k = Ω.conjugate.k := by
  exact Int.natAbs_eq_natAbs_iff.mp (s.angular_order.trans hΩ.symm)

theorem zeroAt_of_signed_pair {n : ℕ} (Ω : AngularCharacter)
    (hΩ : Ω.k.natAbs = n) (Q : Ideal O)
    (a b bΦ Bmask L M ε Z : ℝ) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (Cplus Cminus : ℝ)
    (hp : SignedZeroAt n Ω Q a b bΦ Bmask L M ε Z degree S Cplus)
    (hm : SignedZeroAt n Ω.conjugate Q a b bΦ Bmask L M ε Z degree S Cminus) :
    ZeroAt n (internalQ Q Ω) a b bΦ Bmask L M ε Z degree S (max Cplus Cminus) := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hd := diagonalControl_nonneg s.radial.profile
  have hZ : 0 ≤ Z := zero_le_one.trans s.base_ge_one
  rcases parent_has_one_of_two_types Ω hΩ s with hk | hk
  · apply (hp s hk hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
    gcongr <;> first | exact le_max_left Cplus Cminus | positivity
  · apply (hm s hk hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
    gcongr <;> first | exact le_max_right Cplus Cminus | positivity

theorem eventual_zeroAt_of_all_signed {n : ℕ} (Ω : AngularCharacter)
    (hΩ : Ω.k.natAbs = n) (Q : Ideal O)
    (a b bΦ Bmask L M ε : ℝ) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (h : ∀ Ξ : AngularCharacter, Ξ.k.natAbs = n →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        SignedZeroAt n Ξ Q a b bΦ Bmask L M ε Z degree S C) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      ZeroAt n (internalQ Q Ω) a b bΦ Bmask L M ε Z degree S C := by
  obtain ⟨Cp, hCp, hp⟩ := h Ω hΩ
  obtain ⟨Cm, hCm, hm⟩ := h Ω.conjugate (by simpa using hΩ)
  refine ⟨max Cp Cm, hCp.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hp, hm] with Z hpZ hmZ
  exact zeroAt_of_signed_pair Ω hΩ Q a b bΦ Bmask L M ε Z degree S Cp Cm hpZ hmZ

end OAI.SevenEighths.Angular.NaturalSignedAnchor

#print axioms OAI.SevenEighths.Angular.NaturalSignedAnchor.conjugate_internalQ
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalSignedAnchor.conjugate_internalQ

#print axioms OAI.SevenEighths.Angular.NaturalSignedAnchor.parent_has_one_of_two_types
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalSignedAnchor.parent_has_one_of_two_types

#print axioms OAI.SevenEighths.Angular.NaturalSignedAnchor.zeroAt_of_signed_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalSignedAnchor.zeroAt_of_signed_pair

#print axioms OAI.SevenEighths.Angular.NaturalSignedAnchor.eventual_zeroAt_of_all_signed
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalSignedAnchor.eventual_zeroAt_of_all_signed
