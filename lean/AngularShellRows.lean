import AngularNormalizedSector
import OAI.NumberTheory.DirichletL.Reflection.ShellRows

/-! Exact masked shell source for the angular dyadic row. The source term
retains the actual angular kernel and dual phase; no norm comparison replaces
the physical identity. -/
namespace OAI.CubicEisenstein.AngularShellRows
open scoped Classical BigOperators ContDiff
open SevenEighths ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
open InverseReflectedPhase AngularRawTail AngularRawCoefficient AngularFullRaw AngularFullDyadic
open AngularControlledScalar AngularPhysicalCell
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def angularShellTerm (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4 → ℝ → ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ → ℂ) (θ X : ℝ) : ℂ :=
  AngularPhysicalKernel.actualKernelSourceTerm order F K hK S jF D s hc u m n b windows QK QP Qn Qb W θ X *
    Angular.alpha (fixedCuspArrayIndex u m n b) ^ order

theorem literalRawSeries_eq_shell_source (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1)
    (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    angularLiteralRawSeries order (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
      (u,i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=
    if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
      angularShellTerm order F K hK S jF D s hc u i.1 n.val b.val
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  have hw := shell_windows_one QK QP hQK hQP K (∏ i,S.ideal i) hK.1
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))) hKr hPr i.2.1 i.2.2 n b
  by_cases hp : CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0
  · have hp' : Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0 :=
      ⟨hp.1.1,hp.1.2,hp.2⟩
    rw [ite_eq_left hp]
    unfold angularLiteralRawSeries angularRawDualKernelTerm angularLiteralRawCoefficient literalRawCoefficient angularShellTerm AngularPhysicalKernel.actualKernelSourceTerm actualMixedCoefficient literalRawScale
    rw [ite_eq_left hp',hw]
    dsimp only
    simp only [ramifiedScale,one_mul]
    ring
  · have hp' : ¬(Squarefree n.val ∧ primaryGenerator n.val≠0 ∧ primaryGenerator b.val≠0) :=
      fun h => hp ⟨⟨h.1,h.2.1⟩,h.2.2⟩
    simp only [ite_eq_right hp,angularLiteralRawSeries,angularRawDualKernelTerm,angularLiteralRawCoefficient,literalRawCoefficient,ite_eq_right hp',zero_mul]

theorem literalDyadicBlock_eq_shell_source (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    angularLiteralDyadicBlock order (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
        if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then
          angularShellTerm order F K hK S jF D s hc u i.1 n.val b.val
            (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  exact literalRawSeries_eq_shell_source order F K hK S jF D s hc u i n b QK QP hQK hQP hKr hPr W θ X

theorem literalDyadicBlock_eq_filtered_source (order : ℕ) (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (i : ℕ×ℕ×ℕ) (QK QP : ℝ) (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
    (W : ℝ→ℂ) (θ X : ℝ) :
    angularLiteralDyadicBlock order (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : reflectedNDyad i.2.2, ∑ b : reflectedBDyad i.2.1,
        angularShellTerm order F K hK S jF D s hc u i.1 n.val b.val
          (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X := by
  rw [literalDyadicBlock_eq_shell_source order F K hK S jF D s hc u i QK QP hQK hQP hKr hPr W θ X]
  exact sum_dual_mask i.2.1 i.2.2 (fun n b => angularShellTerm order F K hK S jF D s hc u i.1 n b
    (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X)

#print axioms literalDyadicBlock_eq_filtered_source
end
end OAI.CubicEisenstein.AngularShellRows
