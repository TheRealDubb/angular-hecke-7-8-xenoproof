import AngularTupleRows
import AngularChosenReflection
import OAI.NumberTheory.DirichletL.Reflection.OriginalChosen

/-! Exact reindexing and pullback of the normalized angular source.
Only arithmetic equivalences are reused; angular kernels remain explicit. -/
namespace OAI.CubicEisenstein.AngularSourceTransport
open scoped Classical BigOperators
open SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
open InverseReflectedPhase AngularMixedReflection AngularTupleRows
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}

theorem angularMixed_reindex (order : ℕ) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflected order (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =angularMixedReflected order D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [angularMixedReflected,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]
end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {q : κ→Eis}
    {N a c : Eis} {mode : Bool}

theorem angularMixed_pullback (order : ℕ)
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ k, (Ideal.span {q k}).IsMaximal]
    (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ k, q k≠0) (hc : c≠0)
    (hgp : ∀ i, λ₀∉Ideal.span {p i}) (hgq : ∀ k, λ₀∉Ideal.span {q k})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflected order (pullbackControlled e h D) s hp hc hgp j S W X=
      angularMixedReflected order D s hq hc hgq (fun k => j (e k)) (reindexMarks e S) W X := by
  unfold pullbackControlled
  rw [angularMixedReflected_cast order _ _ s (fun i => hq (e.symm i)) hp hc
    (fun i => hgq (e.symm i)) hgp]
  have hj : (fun i => j (e (e.symm i)))=j := by funext i; simp only [Equiv.apply_symm_apply]
  have he := angularMixed_reindex order D e.symm s hq hc hgq
    (fun k => j (e k)) (reindexMarks e S) W X
  rw [hj,reindexMarks_symm] at he
  exact he
end

section
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T


theorem angular_chosen_reflected_source_eq (order : ℕ) {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    angularMixedReflected order (originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    angularMixedReflected order C s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  unfold originalChosenControlled
  rw [angularMixed_pullback]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
end

#print axioms angular_chosen_reflected_source_eq
end
end OAI.CubicEisenstein.AngularSourceTransport
