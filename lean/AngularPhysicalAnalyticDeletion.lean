import AngularPhysicalSourceRows
import AngularPhysicalSignalIdentity
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalAnalyticDeletion
local notation "O" => ActualEisensteinCubic.O

def factors (M : Ideal O) (ψ : AngularCharacter) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => ψ.idealHom P.val)

theorem factors_eq (M : Ideal O) (ψ : AngularCharacter) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (ψ.idealHom) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : AngularCharacter) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem LFunction_eq_of_mask_right (χ ψ : AngularCharacter)
    (hmask : ∀ I : Ideal O, χ.idealHom I =
      if IsCoprime I χ.modulus then ψ.idealHom I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    FamilyContinuation.LFunction χ s = FamilyContinuation.LFunction ψ s * factors χ.modulus ψ s := by
  rw [FamilyContinuation.LFunction_eq_series χ s hs, FamilyContinuation.LFunction_eq_series ψ s hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (ψ.norm_idealHom_le_one) hmask s hs


theorem LFunction_eq_of_mask_nonzero_order (χ ψ : AngularCharacter)
    (hχ : χ.k≠0) (hψ : ψ.k≠0)
    (hmask : ∀I : Ideal O,χ.idealHom I=if IsCoprime I χ.modulus then ψ.idealHom I else 0)
    {s : ℂ} (hs : 0<s.re) :
    FamilyContinuation.LFunction χ s=FamilyContinuation.LFunction ψ s*factors χ.modulus ψ s := by
  have ha (η : AngularCharacter) (hk : η.k≠0) :
      AnalyticOnNhd ℂ (FamilyContinuation.LFunction η) {z : ℂ | 0<z.re} :=
    (FamilyContinuation.LFunction_differentiable η hk).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt _)
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0<z.re} :=
    (factors_differentiable _ _).differentiableOn.analyticOnNhd (Complex.isOpen_re_gt _)
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (FamilyContinuation.LFunction ψ) (factors χ.modulus ψ) (FamilyContinuation.LFunction χ)
    (ha ψ hψ) hf (ha χ hχ) _ hs
  intro z hz
  exact (LFunction_eq_of_mask_right χ ψ hmask (by simpa using hz)).symm

theorem excludePrimes_mask (η : AngularCharacter) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (I : Ideal O) :
    (η.excludePrimes S hS).idealHom I=
      if IsCoprime I (η.excludePrimes S hS).modulus then η.idealHom I else 0 :=
  η.idealHom_refineModulus _ _ _ I

theorem nonzero_of_excluded (η : AngularCharacter) (hk : η.k≠0)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) {s : ℂ} (hs : 0<s.re)
    (hne : FamilyContinuation.LFunction (η.excludePrimes S hS) s≠0) :
    FamilyContinuation.LFunction η s≠0 := by
  intro hz
  apply hne
  rw [LFunction_eq_of_mask_nonzero_order (η.excludePrimes S hS) η hk hk
    (excludePrimes_mask η S hS) hs,hz,zero_mul]

end OAI.SevenEighths.Angular.PhysicalAnalyticDeletion

#print axioms OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.factors_eq

#print axioms OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.factors_differentiable

#print axioms OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.LFunction_eq_of_mask_right

#print axioms OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.LFunction_eq_of_mask_nonzero_order

#print axioms OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.excludePrimes_mask

#print axioms OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.nonzero_of_excluded
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalAnalyticDeletion.nonzero_of_excluded
