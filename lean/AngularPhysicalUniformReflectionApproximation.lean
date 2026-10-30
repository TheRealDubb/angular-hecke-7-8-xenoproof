import AngularPhysicalUniformReflectionTail
import AngularPhysicalRetainedOriginal
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.UniformReflectionApproximation
open CenteredMomentReflectionDeletion (DecayTwo SmoothIdeal norm norm_pos)
open CenteredMomentReflectionTailMass (dual_scale_bounds)
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open ReflectionMass AnnularFourier RetainedReflection OriginalReflectionApproximation
local notation "O" => ActualEisensteinCubic.O

def retainedSource (χ ψ:AngularCharacter) (a b:ℝ) (ha:0<a) (G:𝓢(ℝ,ℂ)) (X R:ℝ):ℂ :=
  let S:=redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I:SmoothIdeal S,coefficient ψ ψ.conjugate S D I*
    finiteAnnularColumn χ.conjugate (profile ψ.k a b ha G) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))

theorem actual_original_source_approximation (angularOrder:ℕ) (a b xi saving L Cscale ε:ℝ)
    (ha:0<a) (hxi:0<xi) (hscale:0<Cscale) (hε:0<ε):
    ∃H:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀χ:AngularCharacter,
      χ.k.natAbs=angularOrder → (χ.k≠0 ∨ χ.residue≠1) →
      ∃(ψ:AngularCharacter)(g:ℂ),ψ.k=χ.k ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ (ψ.k≠0 ∨ ψ.residue≠1) ∧ ‖g‖=1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
        ∀G:𝓢(ℝ,ℂ),Function.support (G:ℝ→ℂ)⊆Set.Icc a b → ∀X Z:ℝ,
          0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
          ‖Dyadic.polynomial χ false G X 0 0-g*retainedSource χ ψ a b ha G X (Z^(xi/2))‖≤
            C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(χ.modulus.absNorm:ℝ)^ε*Z^(-saving) := by
  obtain ⟨H,C,hC,hbound⟩:=UniformReflectionTail.deleted_discarded_negligible
    angularOrder a b ha xi saving L Cscale ε hxi hscale hε
  refine ⟨H,C,hC,?_⟩
  intro χ hkχ hn
  obtain ⟨ψ,g,hk,hp,hnψ,hg,hcap,hsplit⟩:=original_retained_reflection χ hn
  refine ⟨ψ,g,hk,hp,hnψ,hg,hcap,?_⟩
  intro G hs X Z hX hZ hmod
  let S:=redundantSet χ.modulus ψ.modulus
  have hS:∀P∈S,Prime P:=redundantSet_prime _ _
  have hQ:0<(ψ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap':(ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X:=by
    have h:(ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ):=by
      exact_mod_cast hcap
    exact h.trans hmod
  have hret:retainedSource χ ψ a b ha G X (Z^(xi/2))=
      ∑D∈S.powerset,∑'I:SmoothIdeal S,coefficient ψ ψ.conjugate S D I*
        Dyadic.polynomial χ.conjugate false
          (fun x=>(retainedWeight (Z^(xi/2)) x:ℂ)*profile ψ.k a b ha G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0:=by
    unfold retainedSource
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro I
    rw [finiteAnnularColumn_eq _ _ (profile_decayTwo ψ.k a b ha G) _ _
      (dual_scale_bounds S D hS (Finset.mem_powerset.mp hD) I _ X _ hQ hX hcap').1]
  have he:=hsplit a b ha G hs X (Z^(xi/2)) hX
  dsimp only at he
  rw [he,←hret,mul_add,add_sub_cancel_left,norm_mul,hg,one_mul]
  have hb:=(hbound ψ.k (by rw [hk];exact hkχ) G S hS ψ ψ.conjugate χ.conjugate
    _ X Z hZ hQ hX hcap').2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hε.le

end OAI.SevenEighths.Angular.UniformReflectionApproximation

#print axioms OAI.SevenEighths.Angular.UniformReflectionApproximation.actual_original_source_approximation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformReflectionApproximation.actual_original_source_approximation
