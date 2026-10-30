import AngularPhysicalNaturalCertifiedBand

namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.Angular.NaturalWidth
open EnergyState EnergyBands RelativePrime QuadraticInitialBound NaturalBandTransport
local notation "O" => ActualEisensteinCubic.O
variable {α : Type*}
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable (angularOrder : ℕ)

theorem certified_radial_mono (W : ℝ → ℂ)
    (bslot a b radialOld radialNew Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (hrad : radialNew ≤ radialOld)
    (h : CertifiedBand (α := α) M H hH angularOrder W bslot a b radialOld Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH angularOrder W bslot a b radialNew Bmask L lo hi Mcap κ ε k := by
  obtain ⟨degree, S, hbound⟩ := h
  refine ⟨degree, S, ?_⟩
  intro η₀ hη Q hQM hQ0 hQt hQ72
  obtain ⟨Czero, Cpositive, hCzero, hCpositive, hcert⟩ := hbound η₀ hη Q hQM hQ0 hQt hQ72
  refine ⟨Czero, Cpositive, hCzero, hCpositive, ?_⟩
  filter_upwards [hcert] with Z hZ
  refine ⟨hZ.1, ?_, ?_⟩
  · exact zeroAt_transport _ _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl hrad le_rfl
      le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hZ.2.1
  · exact positiveAt_transport (α := α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl hrad le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hZ.2.2

theorem certified_from_max_two (W : ℝ → ℂ)
    (bslot a b radial Bmask L lo hi Mcap κ ε : ℝ) (k : ℕ)
    (h : CertifiedBand (α := α) M H hH angularOrder W bslot a b (max 2 radial)
      Bmask L lo hi Mcap κ ε k) :
    CertifiedBand (α := α) M H hH angularOrder W bslot a b radial Bmask L lo hi Mcap κ ε k :=
  certified_radial_mono (α := α) M H hH angularOrder W bslot a b (max 2 radial) radial
    Bmask L lo hi Mcap κ ε k (le_max_right _ _) h

end SevenEighths.Angular.NaturalWidth

end

end OAI

#print axioms OAI.SevenEighths.Angular.NaturalWidth.certified_radial_mono
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.certified_radial_mono

#print axioms OAI.SevenEighths.Angular.NaturalWidth.certified_from_max_two
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalWidth.certified_from_max_two
