import AngularPhysicalSecondChildFamily
import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open ChildRows CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
open CenteredMomentSecondEnergySplit (sourceRows sourceRows_nonzero)
local notation "O" => ActualEisensteinCubic.O

lemma physicalBlock_filter_split (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)(p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (rows.filter p) W K n+
      physicalBlock η t S β C D hC hD U R (rows.filter (fun z=>¬p z)) W K n:=by
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not rows p _).symm

def partRows (exceptional:Bool)(η:AngularCharacter)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  (sourceRows C D U R).filter (fun z=>if exceptional then
    ExceptionalRows.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
    else ExceptionalRows.nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)

lemma partRows_false (η:AngularCharacter)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    partRows false η χ Q m C D U R=(sourceRows C D U R).filter (fun z=>
      ¬ExceptionalRows.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z):=by
  ext z
  simp only [partRows,Bool.false_eq_true,ite_false,Finset.mem_filter,ExceptionalRows.nonexceptional]
  exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,sourceRows_nonzero C D U R z h.1,h.2⟩⟩

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_filter_split
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_filter_split

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.partRows_false
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.partRows_false
