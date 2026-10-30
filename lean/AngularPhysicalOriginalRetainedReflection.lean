import AngularPhysicalRetainedReflectionColumns
import AngularPhysicalOriginalConjugateReflection
import AngularPhysicalAnnularFourierLattice

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.RetainedReflection
open CenteredMomentReflectionDeletion (DecayTwo SmoothIdeal norm norm_pos)
open CenteredMomentRetainedReflection (masked_decayTwo)
open CenteredMomentReflectionTailMass (dual_scale_bounds)
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open ReflectionMass AnnularFourier NaturalReflection
local notation "O" => ActualEisensteinCubic.O

theorem original_retained_reflection (χ : AngularCharacter) (hn : χ.k≠0 ∨ χ.residue≠1) :
    ∃(ψ : AngularCharacter)(G : ℂ),ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ (ψ.k≠0 ∨ ψ.residue≠1) ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(a b:ℝ)(ha:0<a)(W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Icc a b → ∀(X R:ℝ)(_hX:0<X),
        let Q := (ψ.modulus.absNorm:ℝ)
        let Y := fun (D : Finset (Ideal O))(H : SmoothIdeal S)=>Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)
        Dyadic.polynomial χ false W X 0 0=
          G*((∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.conjugate S D H*
            Dyadic.polynomial χ.conjugate false
              (fun x=>(retainedWeight R x:ℂ)*profile ψ.k a b ha W x) (Y D H) 0 0)+
            ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.conjugate S D H*
            Dyadic.polynomial χ.conjugate false
              (fun x=>(discardedWeight R x:ℂ)*profile ψ.k a b ha W x) (Y D H) 0 0) := by
  obtain ⟨ψ,G,hk,hp,hnp,hG,hcap,heq⟩ := original_conjugate_reflection χ hn
  refine ⟨ψ,G,hk,hp,hnp,hG,hcap,?_⟩
  intro a b ha W hs X R hX
  dsimp only
  rw [heq a b ha W hs X hX]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := profile_decayTwo ψ.k a b ha W
  have hr := reflected_column_summable _ hS ψ ψ.conjugate χ.conjugate _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.conjugate χ.conjugate _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  rw [←hr.tsum_add hd]
  apply tsum_congr
  intro H
  have hY := (dual_scale_bounds _ D hS (Finset.mem_powerset.mp hD) H
    (ψ.modulus.absNorm:ℝ) X ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈redundantSet χ.modulus ψ.modulus,P):ℝ)/X)
    hQ hX (by rw [div_mul_cancel₀ _ hX.ne'])).1
  change coefficient ψ ψ.conjugate _ D H*Dyadic.polynomial χ.conjugate false
    (profile ψ.k a b ha W) _ 0 0=_
  rw [column_retained_discarded χ.conjugate _ hF R _ hY,mul_add]


end OAI.SevenEighths.Angular.RetainedReflection

#print axioms OAI.SevenEighths.Angular.RetainedReflection.original_retained_reflection
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedReflection.original_retained_reflection
