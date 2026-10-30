import AngularPhysicalEnergyState
import OAI.NumberTheory.DirichletL.Energy.Bands

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.EnergyBands
open EnergyState CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length length_nonneg)
local notation "O" => ActualEisensteinCubic.O
def ZeroAt (angularOrder:ℕ) (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState angularOrder Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

lemma zeroAt_of_zeroBound (angularOrder:ℕ) (Q:Ideal O)(a b bΦ Bmask L M ε Z Z₀:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:ZeroBound angularOrder Q a b bΦ Bmask M ε degree S C Z₀)(hZ:Z₀≤Z):
    ZeroAt angularOrder Q a b bΦ Bmask L M ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ _ _
  exact h Z hZ s hQ hs p t X₁ X₂ hX₁ hX₂

end OAI.SevenEighths.Angular.EnergyBands

#print axioms OAI.SevenEighths.Angular.EnergyBands.zeroAt_of_zeroBound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.EnergyBands.zeroAt_of_zeroBound
