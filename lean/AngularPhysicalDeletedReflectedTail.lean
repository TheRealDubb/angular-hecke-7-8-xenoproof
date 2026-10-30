import AngularPhysicalReflectionColumn
import AngularPhysicalReflectedNegligible

noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.SevenEighths.Angular.ReflectionTails
open ReflectionMass
open CenteredMomentReflectionDeletion (SmoothIdeal norm)
open CenteredMomentReflectionTailMass (dual_scale_bounds)
local notation "O" => ActualEisensteinCubic.O

theorem actual_deleted_discarded_negligible (angularOrder:ℕ) (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs:Function.support W⊆Set.Icc a b,∀hW:ContDiff ℝ ∞ W,
      ∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
        (η ηi χ : AngularCharacter)(t Q X Z : ℝ),1≤Z → 0<Q → 0<X →
        Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
        let F := fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          AnnularFourier.profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) x
        (∀D∈S.powerset,Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
          Dyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0)) ∧
        ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*
          Dyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0‖≤
          C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_reflected_upper_negligible angularOrder a b xi saving L Cscale ha hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound ε hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro k hk S hS η ηi χ t Q X Z hZ hQ hX hcap
  dsimp only
  have hh := hDb S hS η ηi
    (fun E H=>Dyadic.polynomial χ false
      (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
        AnnularFourier.profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*(1+‖t‖)^n*Z^(-saving)) (by positivity) (by
      intro E hE H
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X (Cscale*Z^L) hQ hX hcap
      exact hCb k hk χ t _ Z hZ hy.1 hy.2)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring


end OAI.SevenEighths.Angular.ReflectionTails

#print axioms OAI.SevenEighths.Angular.ReflectionTails.actual_deleted_discarded_negligible
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionTails.actual_deleted_discarded_negligible
