import AngularPhysicalNaturalRow

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.NaturalRows
local notation "O" => ActualEisensteinCubic.O

def naturalCharacter (η:AngularCharacter) (z:O) : AngularCharacter :=
  if h:z≠0 then (naturalRow η z h).character else η

lemma naturalCharacter_eq (η:AngularCharacter) (z:O) (hz:z≠0) :
    naturalCharacter η z=(naturalRow η z hz).character := by
  simp [naturalCharacter,hz]

theorem naturalCharacter_k (η:AngularCharacter) (z:O) :
    (naturalCharacter η z).k=η.k := by
  by_cases hz:z≠0
  · rw [naturalCharacter_eq η z hz]
    exact (naturalRow η z hz).angular_type
  · simp [naturalCharacter,hz]

theorem naturalCharacter_order (η:AngularCharacter) (z:O) :
    (naturalCharacter η z).k.natAbs=η.k.natAbs :=
  congrArg Int.natAbs (naturalCharacter_k η z)

end OAI.SevenEighths.Angular.NaturalRows

#print axioms OAI.SevenEighths.Angular.NaturalRows.naturalCharacter_k
#print axioms OAI.SevenEighths.Angular.NaturalRows.naturalCharacter_order
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.naturalCharacter_order
