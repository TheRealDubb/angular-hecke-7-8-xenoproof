import AngularPhysicalOriginalReflectionCoefficients

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.NaturalReflection
open CenteredMomentNaturalPrimitive NaturalPrimitive PlainDeletion AnnularReflection AnnularFourier
open CenteredMomentReflectionDeletion (SmoothIdeal norm)
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem original_natural_reflection (χ:AngularCharacter) (hn:χ.k≠0 ∨ χ.residue≠1) :
    ∃(ψ:AngularCharacter)(G:ℂ),ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (ψ.k≠0 ∨ ψ.residue≠1) ∧ ‖G‖=1 ∧
      let S:=redundantSet χ.modulus ψ.modulus
      let hS:=redundantSet_prime χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      (∀I,χ.idealHom I=(ψ.excludePrimes S hS).idealHom I) ∧
      ∀(a b:ℝ)(ha:0<a)(W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Icc a b →
      ∀X:ℝ,0<X →
        (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W)
          X (ψ.modulus.absNorm:ℝ) D)) ∧
        Dyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H:SmoothIdeal S,
            reflectedTerm ψ ψ.conjugate S hS (profile ψ.k a b ha W) X (ψ.modulus.absNorm:ℝ) D H := by
  obtain ⟨ψ,hk,hmod,hprim,hne,hsq,hcop,hdvd,hnorm,hcoeff⟩:=NaturalPrimitive.exists_natural_primitive χ
  obtain ⟨G,hG,hreflection⟩:=primitive_character_deleted ψ hprim (hne hn)
  refine ⟨ψ,G,hk,hprim,hne hn,hG,hnorm,hcop,hcoeff,?_⟩
  intro a b ha W hs X hX
  have hh:=hreflection _ (redundantSet_prime χ.modulus ψ.modulus) a b ha W hs X hX
  exact ⟨hh.1,(polynomial_coeff_congr χ _ hcoeff W X).trans hh.2⟩

theorem original_conjugate_reflection (χ:AngularCharacter) (hn:χ.k≠0 ∨ χ.residue≠1) :
    ∃(ψ:AngularCharacter)(G:ℂ),ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (ψ.k≠0 ∨ ψ.residue≠1) ∧ ‖G‖=1 ∧
      let S:=redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(a b:ℝ)(ha:0<a)(W:𝓢(ℝ,ℂ)),Function.support (W:ℝ→ℂ)⊆Set.Icc a b →
      ∀X:ℝ,0<X →
        Dyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H:SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*ψ.idealHom (∏P∈D,P)*
              ψ.conjugate.idealHom H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              Dyadic.polynomial χ.conjugate false (profile ψ.k a b ha W)
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hk,hprim,hne,hG,hnorm,hcop,hcoeff,hreflect⟩:=original_natural_reflection χ hn
  refine ⟨ψ,G,hk,hprim,hne,hG,hnorm,?_⟩
  intro a b ha W hs X hX
  rw [(hreflect a b ha W hs X hX).2]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  unfold reflectedTerm
  rw [←polynomial_coeff_congr χ.conjugate _
    (conjugate_deletion_coeff χ ψ _ (redundantSet_prime χ.modulus ψ.modulus) hcoeff)]

end OAI.SevenEighths.Angular.NaturalReflection

#print axioms OAI.SevenEighths.Angular.NaturalReflection.original_natural_reflection
#print axioms OAI.SevenEighths.Angular.NaturalReflection.original_conjugate_reflection
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReflection.original_conjugate_reflection
