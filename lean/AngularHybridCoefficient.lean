import AngularPhaseSeparation
import OAI.NumberTheory.DirichletL.Reflection.Canonical
import OAI.NumberTheory.DirichletL.Reflection.Independent

/-! The actual quadratic/cubic coefficient factorization with the added
angular column weight. Common sector coefficients remain independent of the
moving row, and the added factor cannot increase a column's norm. -/

noncomputable section
open scoped Classical BigOperators
namespace OAI.CubicEisenstein.AngularHybridCoefficient
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open SevenEighths.Angular SevenEighths.InverseMoment SevenEighths.InverseReflectedPhase
open AngularPhaseSeparation
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
section
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

def angularSourceColumn (order : ℕ) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  sourceColumn D s hc hg j F u m n b * alpha (fixedCuspArrayIndex u m n b) ^ order

theorem angularSourceColumn_norm_le (order : ℕ) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖angularSourceColumn order D s hc hg j F u m n b‖ ≤ ‖sourceColumn D s hc hg j F u m n b‖ :=
  angular_column_product_bound _ _ _

theorem angular_mixed_coefficient_hybrid (order : ℕ) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (s.amplitude u m n b * alpha (fixedCuspArrayIndex u m n b) ^ order) *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg j R F u m * sourceSlotPhase s hp hg j S F u m *
      sourceFrozenPhase D s hp hg j F u m) *
      angularSourceColumn order D s hc hg j F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have he := mixed_coefficient_hybrid_original_exponents D s hp hc hg hcop hprimary
    R S F hRS hF hu j hRj hR u m n b hb
  unfold angularSourceColumn
  linear_combination alpha (fixedCuspArrayIndex u m n b) ^ order * he

end

theorem canonical_common_angular_coefficients (order : ℕ) {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, (G x).ideal (f x i)=(G y).ideal (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (G x).generator_ne_zero (G x).generator_good
          (j x) (F.image (f x)) u m =
          γ (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m) ∧
        ∀ x u m n b, angularSourceColumn order (E x) s hc (G x).generator_good (j x) (F.image (f x)) u m n b =
          β (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  obtain ⟨E, γ, β, hγ, hβ⟩ := canonical_common_reflected_coefficients G N a c mode s
    hc hN hbase hac hcop hNp j f hf hfixed hjfixed F fixedIdeal row slot hprod
  refine ⟨E, γ, (fun q u m n b => β q u m n b * alpha (fixedCuspArrayIndex u m n b) ^ order), hγ, ?_⟩
  intro x u m n b
  unfold angularSourceColumn
  rw [hβ]

#print axioms angular_mixed_coefficient_hybrid
#print axioms canonical_common_angular_coefficients
end OAI.CubicEisenstein.AngularHybridCoefficient
