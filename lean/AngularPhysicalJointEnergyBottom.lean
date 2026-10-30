import AngularPhysicalPositiveEnergyBands
import AngularPhysicalEnergyFloor

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.EnergyBands
open EnergyState RelativePrime InductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance angularJointBottomFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/- Both base cases use one degree and one finite seminorm set, chosen before
the anchor, fixed modulus, row, and smooth profiles. No child estimate is assumed. -/
theorem exists_joint_bottom (angularOrder : ℕ)
    (W : ℝ → ℂ) (aslot bslot : ℝ) (haslot : 0 < aslot)
    (hWs : Function.support W ⊆ Set.Icc aslot bslot) (hW : ContDiff ℝ ∞ W)
    (a b bΦ Bmask L Lslot lo hi ε κ : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hbΦ : 0 < bΦ) (hmask : 0 ≤ Bmask)
    (hε : 0 < ε) (hLs : 0 ≤ Lslot) (hκ : (3/4 : ℝ) ≤ κ) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ Czero Cpositive : ℝ,
      0 < Czero ∧ 0 < Cpositive ∧
      ∀ η₀ : AngularCharacter, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ∀ Q : Ideal O, Q ≤ M →
          ZeroAt angularOrder (internalQ Q η₀) a b bΦ Bmask L
            (ε/16) ε Z degree S Czero ∧
          PositiveAt (α := α) M H hH angularOrder W bslot a b bΦ Bmask L Lslot lo hi
            (ε/16) ε κ Z η₀ Q degree S Cpositive := by
  obtain ⟨d₀, S₀, C₀, hC₀, hzero⟩ :=
    exists_zero_floor angularOrder a b bΦ Bmask ε ha hb hbΦ hmask hε
  obtain ⟨d₁, S₁, C₁, hC₁, hpositive⟩ :=
    exists_positive_bottom (α := α) M H hH angularOrder W aslot bslot haslot hWs hW
      a b bΦ Bmask L Lslot lo hi ε κ ha hb hbΦ hmask hε hLs hκ
  have hcontrol (p : Profiles a b) (S T : Finset (ℕ × ℕ)) (hST : S ⊆ T) :
      p.control S ≤ p.control T := by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  refine ⟨d₀ + d₁, S₀ ∪ S₁, C₀, C₁, hC₀, hC₁, ?_⟩
  intro η₀
  filter_upwards [hpositive η₀] with Z hZ
  have hZ0 : 0 ≤ Z := (zero_lt_one.trans hZ.1).le
  refine ⟨hZ.1, ?_⟩
  intro Q hQM
  constructor
  · have hz := zeroAt_of_zeroBound angularOrder (internalQ Q η₀) a b bΦ Bmask L
      (ε/16) ε Z 1 d₀ S₀ C₀ (hzero (internalQ Q η₀)) hZ.1.le
    intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hh := hz s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
    have hctrl := hcontrol p S₀ (S₀ ∪ S₁) Finset.subset_union_left
    have hpow : (1 + ‖t‖)^d₀ ≤ (1 + ‖t‖)^(d₀ + d₁) :=
      pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right _ _)
    have hd := diagonalControl_nonneg s.radial.profile
    have hp := p.control_nonneg S₀
    have hp' := p.control_nonneg (S₀ ∪ S₁)
    apply hh.trans
    gcongr
  · have hp := hZ.2 Q hQM
    intro T θ w σ v t height hw hwL hσlo hσhi hheight hv
      s hanchor hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
    have hh := hp T θ w σ v t height hw hwL hσlo hσhi hheight hv
      s hanchor hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
    have hctrl := hcontrol p S₁ (S₀ ∪ S₁) Finset.subset_union_right
    have hpow : (1 + |t| + height)^d₁ ≤ (1 + |t| + height)^(d₀ + d₁) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.le_add_left _ _)
    have hd := diagonalControl_nonneg s.radial.profile
    have hc := p.control_nonneg S₁
    have hc' := p.control_nonneg (S₀ ∪ S₁)
    apply hh.trans
    gcongr

end OAI.SevenEighths.Angular.EnergyBands

#print axioms OAI.SevenEighths.Angular.EnergyBands.exists_joint_bottom
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyBands.exists_joint_bottom
