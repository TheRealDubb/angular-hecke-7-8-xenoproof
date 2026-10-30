import AngularPhysicalFixedQForcingCount

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.FixedQForcingCount
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentForcing CenteredMomentRankinRadical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentSupport CenteredMomentSourceRow
open UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentFixedQForcingCount
open CenteredMomentSecondExceptionalCount (common_prime_prime common_prime_dvd_left)
open ChildRows
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_canonical_exceptional_count_fixedQ (η : AngularCharacter) (χ : RayFourExpansion.RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hη : η.idealHom C ≠ 0)
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, ExceptionalRows.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card:ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D => P.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6)) := by
  have he : η.elementCoeff (primaryGenerator C) ≠ 0 := by
    rw [←η.idealHom_span (primaryGenerator C),primary_span_supported C hC]
    exact hη
  have hinj : Function.Injective (fun P:CommonIndex C D => Ideal.span {commonPrime C D P}) := by
    simpa only [commonPrime_span C D hC] using
      (Subtype.val_injective : Function.Injective (fun P:CommonIndex C D => P.val))
  have hb := FixedQForcingCount.actual_forcing_exceptional_count_fixedQ (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P _
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb


end OAI.SevenEighths.Angular.FixedQForcingCount

#print axioms OAI.SevenEighths.Angular.FixedQForcingCount.actual_canonical_exceptional_count_fixedQ
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FixedQForcingCount.actual_canonical_exceptional_count_fixedQ
