import AngularPhysicalMarkedDeletion
import AngularPhysicalMarkedDeletedEnergy

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Angular.MarkedReference
open InverseRows OAI.SevenEighths.Angular.Dyadic CubicEisenstein.AngularRawCoefficientGates
open InverseInitialPhysicalSlots InverseMoment IdealMobiusDivisorSum
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem physical_reference_energy (angularOrder : ℕ) {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D)
    (W : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao) (hab : ao ≤ bo)
    (hsW : Function.support W ⊆ Set.Icc ao bo) (hW : ContDiff ℝ ∞ W)
    (εm : ℝ) (hεm : 0 < εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, data.η.k = (angularOrder : ℤ) →
    ∃ C U₀ : ℝ, 0 < C ∧ 1 < U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
    ∀ {ι : Type} [Fintype ι], Fintype.card ι ≤ K →
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (ell : ι → ℝ) (ζ : ι → ℂ),
      (∀ i, 0 ≤ ell i) → (∀ i, (ζ i).re ≤ 1) →
      (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => livePrimes M H F.W 2 (U^(ell i)))) →
      (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < U^(ell i)) →
    ∀ r : ℝ, 0 ≤ r → r + 2*(∑ i, ell i) < 1 → 2*r + 8*(∑ i, ell i) < 3 →
    ∀ rows : Finset NonzeroElement,
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) → ∀ θ : ℝ,
      (∑ u ∈ rows, ‖polynomial (data.character u) true (childLogTest W θ) (U^r) 0 0 *
        (∏ i, HeckePrimeRow.canonicalPrimeAmplitude M H u.val F.W 2 (U^(ell i)) (ζ i))‖^2) ≤
        C * U^(1+εm) * ((1+‖θ‖)^degree)^2 := by
  obtain ⟨degree, henergy⟩ := deleted_source_energy angularOrder F W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree, ?_⟩
  intro data hk
  obtain ⟨C, U₀, hC, hU₀, he⟩ := henergy data hk
  let Tbad := idealDivisors (∏ P ∈ excluded data, P)
  let Ctotal : ℝ := ((Tbad.card : ℝ)+1)^2*C
  refine ⟨Ctotal, U₀, by dsimp [Ctotal]; positivity, hU₀, ?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond rows hrows θ
  have hUone : 1 < U := hU₀.trans_le hU
  have hUp : 0 < U := zero_lt_one.trans hUone
  have hw : ∀ x, childLogTest W θ x ≠ 0 → x ≤ bo := by
    intro x hx
    apply (hsW (show x ∈ Function.support W from ?_)).2
    intro hz
    exact hx (by simp only [childLogTest, hz, zero_mul])
  have hphys := physical_rows_le_deleted_sources data rows M H
    (childLogTest W θ) (fun _ : ι => F.W) U r 0 0 bo (fun _ => 1) (fun _ => 2) ell ζ
    hUone hw (fun _ => F.complex_support) (by simpa only [one_mul] using hlarge)
  let imageRows : Finset O := rows.image (fun u => u.val)
  have hsum (f : O → ℝ) : (∑ u ∈ imageRows, f u) = ∑ u ∈ rows, f u.val :=
    Finset.sum_image (fun u _ w _ heq => Subtype.ext heq)
  have himage : ∀ u ∈ imageRows, ‖eisEmbedding u‖^2 ≤ U := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrows w hw
  have hterm (j : Ideal O) (hj : j ∈ Tbad) :
      (∑ u ∈ rows, ‖deletedSelectedSource data M H (childLogTest W θ) (fun _ : ι => F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _ => 2) ell ζ u.val‖^2) ≤
          C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
    have hh := he U hU hK M H ell ζ hell hζ hdis hlarge r hr hfirst hsecond
      j hj imageRows himage θ
    rwa [hsum] at hh
  refine hphys.trans ?_
  change (Tbad.card : ℝ)*(∑ j ∈ Tbad, _) ≤ _
  calc
    _ ≤ (Tbad.card : ℝ)*(∑ j ∈ Tbad, C*U^(1+εm)*((1+‖θ‖)^degree)^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (Tbad.card : ℝ)^2*C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ Ctotal*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0 ≤ (Tbad.card : ℝ) by positivity]

#print axioms physical_reference_energy
end SevenEighths.Angular.MarkedReference
end
end OAI
