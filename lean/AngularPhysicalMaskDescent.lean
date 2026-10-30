import AngularPhysicalExceptionalReflection

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open HeckeMaskDescent (exists_coprime_shift)
local notation "O" => ActualEisensteinCubic.O

theorem descent_of_mask (χ χ' ψ : AngularCharacter) (htype : ψ.k=χ.k) (r : O) (hr : r ≠ 0)
    (he : ∀ n, χ'.elementCoeff n =
      if IsCoprime n r then χ.elementCoeff n else 0)
    (hind : InducedBy χ' ψ) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (ψ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a = (u : O ⧸ χ.modulus) := by
    dsimp [a];rw [map_add,map_one,hqu];ring
  have hψa : Ideal.Quotient.mk ψ.modulus a = 1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  let c := idealGenerator (χ.modulus*ψ.modulus)
  have hc : IsCoprime a c := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [show Ideal.span {c}=χ.modulus*ψ.modulus from span_idealGenerator _]
    apply IsCoprime.mul_right
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hψa ▸ isUnit_one)
  obtain ⟨t,htall⟩ := exists_coprime_shift a c (r*goodLambda) hc
    (mul_ne_zero hr goodLambda_prime.ne_zero)
  have ht := htall.of_mul_right_left
  let n := a+t*c
  have hmem : c ∈ χ.modulus*ψ.modulus := by
    rw [← span_idealGenerator (χ.modulus*ψ.modulus)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnχ : Ideal.Quotient.mk χ.modulus n = (u : O ⧸ χ.modulus) := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left hmem),mul_zero,add_zero,ha]
  have hnψ : Ideal.Quotient.mk ψ.modulus n = 1 := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hmem),mul_zero,add_zero,hψa]
  have hn0 : n ≠ 0 := by
    intro hz
    have hunit : IsUnit goodLambda := (htall.of_mul_right_right).isUnit_of_dvd'
      (by change goodLambda ∣ n; rw [hz]; exact dvd_zero _) (dvd_refl _)
    exact goodLambda_prime.not_isUnit hunit
  have hnχ' : χ'.elementCoeff n ≠ 0 := by
    rw [he n,ite_eq_left ht,χ.elementCoeff_eq hn0]
    exact mul_ne_zero (zpow_ne_zero _ (alpha_ne_zero hn0)) (MulChar.apply_ne_zero_iff.mpr (hnχ ▸ u.isUnit))
  have hcop : IsCoprime (Ideal.span {n}) χ'.modulus :=
    ChildRows.old_coefficient_nonzero_coprime χ' n hnχ' 
  have heq := elementCoeff_eq_of_inducedBy χ' ψ hind n hcop
  rw [he n,ite_eq_left ht] at heq
  rw [χ.elementCoeff_eq hn0,ψ.elementCoeff_eq hn0,htype,hnχ,hnψ,map_one,mul_one] at heq
  exact mul_left_cancel₀ (zpow_ne_zero _ (alpha_ne_zero hn0)) (by simpa only [mul_one] using heq)

theorem inducedBy_mask (χ χ' ψ : AngularCharacter) (r : O)
    (he : ∀ n, χ'.elementCoeff n =
      if IsCoprime n r then χ.elementCoeff n else 0)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  intro I
  by_cases hI : I = 0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn' := idealHom_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    let n := idealGenerator I
    have hn0 : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hval' : χ'.elementCoeff n = χ'.idealHom I := by
      rw [← χ'.idealHom_span,hspan]
    have hval : χ.elementCoeff n = χ.idealHom I := by
      rw [← χ.idealHom_span,hspan]
    have hm := he n
    have hcr : IsCoprime n r := by
      by_contra hr
      rw [ite_eq_right hr,hval'] at hm
      exact hn' hm
    rw [ite_eq_left hcr,hval',hval] at hm
    have hn := hm ▸ hn'
    have hcχ := (idealHom_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hm,hind I,ite_eq_left hcχ]
  · have hz : χ'.idealHom I = 0 := by
      by_contra hn
      exact hc ((idealHom_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixed_inducing_mask_iff (χ χ' : AngularCharacter) (htype : χ'.k=χ.k)
    (r : O) (hr : r≠0)
    (he : ∀ n, χ'.elementCoeff n=if IsCoprime n r then χ.elementCoeff n else 0)
    (Q : Ideal O) :
    (∃ ψ : AngularCharacter, ψ.k=χ'.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q≤ψ.modulus ∧ InducedBy χ' ψ) ↔
    (∃ ψ : AngularCharacter, ψ.k=χ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q≤ψ.modulus ∧ InducedBy χ ψ) := by
  constructor
  · rintro ⟨ψ,hψk,hprim,hQ,hind⟩
    obtain ⟨ρ,hρk,hρ,hmod,hindρ⟩ := exists_primitive_above χ ψ.modulus
      (descent_of_mask χ χ' ψ (hψk.trans htype) r hr he hind)
    exact ⟨ρ,hρk,hρ,hQ.trans hmod,hindρ⟩
  · rintro ⟨ψ,hψk,hprim,hQ,hind⟩
    exact ⟨ψ,hψk.trans htype.symm,hprim,hQ,inducedBy_mask χ χ' ψ r he hind⟩

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixed_inducing_mask_iff
