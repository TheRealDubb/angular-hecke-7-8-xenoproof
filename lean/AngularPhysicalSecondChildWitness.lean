import AngularPhysicalSecondDyadicRows
import OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondLiveBlock (liveRows)
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
theorem physicalBlock_live_dyadic_witness (η:AngularCharacter)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩


theorem actual_dyad_ge_one (η:AngularCharacter)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    1≤dyadicScale (n 1) := by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U
    R rows W K n hne
  exact (normValue_ge_one z hz0).trans (dyadicRows_norm rows n z hz).2.le

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.actual_dyad_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.actual_dyad_ge_one
