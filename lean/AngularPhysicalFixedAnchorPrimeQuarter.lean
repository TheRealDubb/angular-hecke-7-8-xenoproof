import AngularPhysicalFixedRayAnchor
import AngularPhysicalActualRelativePrimeBound

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter
namespace OAI.SevenEighths.Angular.RelativePrime
open NaturalRows ExceptionalRows
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentSecondHeightFamily (fixedBadMask)
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance fixedAnchorQuarterFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Opposite angular types cancel before the original finite-order theorem is
used. The constant and height degree precede the anchor; its modulus may affect
the scale threshold. This is a prime-slot estimate, not angular nonvanishing. -/
theorem fixed_anchor_prime_three_quarters (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi : ℝ) (hLm : 0 ≤ Lmod) (hLs : 0 ≤ Lslot)
    (hloss : 0 < loss) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ Ω : AngularCharacter, ∃ Z₀ : ℝ, 1 < Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ θ : RayQuotient.Characters M H,
      ∀ P : ℝ, 1 ≤ P → P ≤ Z^Lslot → ∀ η : AngularCharacter, η.k = Ω.k → ∀ z : O,
      ∀ F : NaturalRow η z, (F.character.modulus.absNorm : ℝ) ≤ Z^Lmod →
      ∀ Q : Ideal O, Q ≤ M → ¬FixedInducingRow η (internalQ Q Ω) fixedBadMask 1 z →
      ∀ σ t v : ℝ, lo ≤ σ → σ ≤ hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I => (rayRelativeCharacter M H hH Ω θ).idealHom I *
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2 ≤
        C * (1+|t|+|v|)^degree * Z^loss * P^(3/4 : ℝ) := by
  obtain ⟨degree, C, hC, hbound⟩ := natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi hLm hLs hloss
  refine ⟨degree, C, hC, ?_⟩
  intro Ω
  have hev : ∀ᶠ Z : ℝ in atTop, ∀ θ : RayQuotient.Characters M H, _ :=
    Filter.eventually_all.mpr (fun θ => hbound (rayRelativeCharacter M H hH Ω θ))
  obtain ⟨Zbase, hbase⟩ := eventually_atTop.mp hev
  refine ⟨max 2 Zbase, lt_max_of_lt_left (by norm_num), ?_⟩
  intro Z hZ θ P hP hPcap η hη z F hcond Q hQM hex σ t v hσ hσhi
  obtain ⟨hfloor, hupper, hceil, hκ⟩ := seven_eighths_prime_ceiling
  exact hbase Z ((le_max_right _ _).trans hZ) θ _ _ hfloor hupper hceil hκ.le
    P hP hPcap η z F (ray_inverse_anchor_cancels_type M H hH Ω η hη θ) hcond
    (internalQ Q Ω) (inf_le_left.trans hQM)
    (internalQ_le_relative_modulus M H hH Q hQM Ω θ) hex σ t v hσ hσhi

end OAI.SevenEighths.Angular.RelativePrime

#print axioms OAI.SevenEighths.Angular.RelativePrime.fixed_anchor_prime_three_quarters
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RelativePrime.fixed_anchor_prime_three_quarters
