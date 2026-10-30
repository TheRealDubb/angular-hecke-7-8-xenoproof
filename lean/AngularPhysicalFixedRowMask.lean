import AngularPhysicalMaskDescent

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalRows
open PrimaryVolume (InducedBy)
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open HeckeMaskDescent (exists_coprime_shift)
local notation "O" => ActualEisensteinCubic.O

theorem row_mask_mul (η : AngularCharacter) (m r A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist η.elementHom.toMonoidHom (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist η.elementHom.toMonoidHom m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs,
      rowTwist_extract_sixth_mask _ _ _ _ _ hs]
    change η.elementCoeff n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask,hm,hr,AngularCharacter.elementHom,
        show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) hs,
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs]
    split_ifs <;> rfl

theorem fixedInducingRow_mul_mask_iff (η : AngularCharacter) (Q : Ideal O)
    (m r A z : O) (hm : m≠0) (hr : r≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχk,_,hχ,_⟩ := AngularRowClosure.exists_angular_row_character
    η m 1 (A*z) hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2
  obtain ⟨χ',hχ'k,_,hχ',_⟩ := AngularRowClosure.exists_angular_row_character
    η (m*r) 1 (A*z) (mul_ne_zero hm hr) one_ne_zero (mul_ne_zero hA hz)
      (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _))
  have hmask (n : O) : χ'.elementCoeff n=if IsCoprime n r then χ.elementCoeff n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : AngularCharacter) (mask : O) (hρk : ρ.k=η.k)
      (hρ : ∀ n,ρ.elementCoeff n=rowTwist η.elementHom.toMonoidHom mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : AngularCharacter, ψ.k=ρ.k ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q≤ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,_,hψk,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hψk.trans hρk.symm,hprim,hQ,inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (fun n => (hρ n).trans (hρ₀ n).symm) hind⟩
    · rintro ⟨ψ,hψk,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hρk,hψk.trans hρk,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ'k hχ',transport χ m hχk hχ]
  exact fixed_inducing_mask_iff χ χ' (hχ'k.trans hχk.symm) r hr hmask Q

theorem fixed_mask_change (η : AngularCharacter) (Q : Ideal O) (m n A z : O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:goodLambda∣m) (hm2:(2:O)∣m) (hnLam:goodLambda∣n) (hn2:(2:O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1 := fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2 := fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2

end OAI.SevenEighths.Angular.ExceptionalRows

#print axioms OAI.SevenEighths.Angular.ExceptionalRows.fixed_mask_change
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalRows.fixed_mask_change
