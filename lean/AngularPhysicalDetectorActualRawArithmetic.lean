import AngularPhysicalDetectorActualInitialCoefficient
import OAI.NumberTheory.DirichletL.Detector.RawIndexGrouping

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CubicEisenstein ProbePhysical ProbeMellinBoundary
open HeckeFamily HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

open CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
open scoped ContDiff

def rawArithmeticSeries (S : Finset (Ideal O)) (D : Ideal O) (η : AngularCharacter)
    (C : CalibrationData) (x w z : ℂ) : ℂ :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

lemma rawHighCoefficient_outer_support (S : Finset (Ideal O)) (D : Ideal O) (η : AngularCharacter)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    intro hz
    exact hp (by simp only [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,bareIdealHighSummand,hz,mul_zero,zero_mul])
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw (S : Finset (Ideal O)) (D : Ideal O) (η : AngularCharacter)
    (C : CalibrationData) (x w z : ℂ) :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := by
  unfold rawArithmeticSeries sourceRawEmbedding
  change _ = ∑'i : {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}, _
  symm
  apply tsum_subtype_eq_of_support_subset (f:=fun p : RawHighIndex=>
    fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val)) x w z (rawHighEmbedding p))
    (s:={p : RawHighIndex | Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2})
  intro p hp
  exact rawHighCoefficient_outer_support S D η _ x w z p hp


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.rawHighCoefficient_outer_support

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.rawArithmeticSeries_eq_sourceRaw
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.rawArithmeticSeries_eq_sourceRaw
