import AngularPhysicalNaturalCharacter
import AngularPhysicalEnergyState
import OAI.NumberTheory.DirichletL.Energy.ReferenceState

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ReferenceState
open ConcreteTraceCRT EnergyState NaturalRows
open CenteredMomentNaturalRowSource (fixedConductorFactor)
open CenteredMomentEnergyReferenceState (effectiveRadial)
local notation "O" => ActualEisensteinCubic.O

def effectiveState {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ):NaturalState angularOrder Z Bmask bΦ:=
  {s with radial:=effectiveRadial s.radial
          row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
          nonexceptional:=fun z hz=>s.nonexceptional z hz.1}

lemma effective_row_norm {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth:=by
  rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
  exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hz.2)

lemma effective_character_nonprincipal {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    (naturalCharacter s.character z).k≠0 ∨ (naturalCharacter s.character z).residue≠1:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  exact (naturalRow s.character z hn).nonprincipal hn s.fixedModulus s.puncture
    s.puncture_ne_zero (s.nonexceptional z hz.1)

lemma effective_character_cap {angularOrder:ℕ} {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)(hbΦ:0≤bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*bΦ*Z^s.width:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  have h:=(naturalRow s.character z hn).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans_le s.base_ge_one) hbΦ s.modulus_bound (effective_row_norm s z hz)
  simpa only [NaturalState.width,add_comm s.characterWidth s.rowWidth] using h


theorem effective_character_order {angularOrder:ℕ} {Z Bmask bΦ:ℝ}
    (s:NaturalState angularOrder Z Bmask bΦ) (z:O) :
    (naturalCharacter s.character z).k.natAbs=angularOrder :=
  (naturalCharacter_order s.character z).trans s.angular_order

theorem effectiveState_order {angularOrder:ℕ} {Z Bmask bΦ:ℝ}
    (s:NaturalState angularOrder Z Bmask bΦ) :
    (effectiveState s).character.k.natAbs=angularOrder := s.angular_order

end OAI.SevenEighths.Angular.ReferenceState

#print axioms OAI.SevenEighths.Angular.ReferenceState.effective_character_nonprincipal
#print axioms OAI.SevenEighths.Angular.ReferenceState.effective_character_cap
#print axioms OAI.SevenEighths.Angular.ReferenceState.effective_character_order
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReferenceState.effective_character_order
