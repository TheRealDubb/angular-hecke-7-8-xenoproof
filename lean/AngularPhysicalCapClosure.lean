import AngularPhysicalZeroSupremum
import AngularFamilyConjugation
import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing

/- The signed finite-cap closure. The negative-order analytic improvement is
an explicit premise, not an axiom or a completed public theorem. The k=0
base uses the pinned original theorem only after exact finite identification. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalCapClosure
open PhysicalZeroSupremum

theorem typeZero_nonzero (χ : AngularCharacter) (hk : χ.k=0) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : χ.residue=1 → s≠1) :
    FamilyContinuation.LFunction χ s≠0 := by
  have hp : ¬((FiniteIdentification.toFinite χ hk).residue=1 ∧ s=1) := by
    rintro ⟨hr,h1⟩
    exact hpole hr h1
  by_cases hr : χ.residue=1
  · rw [FiniteIdentification.typeZero_LFunction χ hk s
      (by intro h; norm_num [h] at hs) (hpole hr)]
    exact HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re _ hs hp
  · rw [TypeZeroEntire.LFunction_eq_finite χ hk hr s]
    exact HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re _ hs hp

theorem beta_zero_le : beta 0≤(7/8:ℝ) := by
  apply beta_le_of_half_plane 0 (7/8) (by norm_num)
  intro χ s hn hs hpole
  have hk : χ.k=0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
  exact typeZero_nonzero χ hk s hs (hpole hk)

/-- The remaining analytic supplier must give one positive saving before
the character, for each fixed positive angular order and its actual cap.
Conjugation and induction then handle both signs and all smaller orders. -/
def NegativeOrderImprovement : Prop :=
  ∀n : ℕ,0<n → (7/8:ℝ)<beta n →
    ∃δ : ℝ,0<δ ∧ ∀χ : AngularCharacter,χ.k= -(n:ℤ) →
      ∀s : ℂ,beta n-δ<s.re → FamilyContinuation.LFunction χ s≠0

theorem beta_le_of_negative_order_improvement (h : NegativeOrderImprovement) :
    ∀n : ℕ,beta n≤(7/8:ℝ) := by
  intro n
  induction n with
  | zero => exact beta_zero_le
  | succ n ih =>
      apply beta_le_of_uniform_improvement (n+1) (7/8) (by norm_num)
      intro hbeta
      obtain ⟨δ,hδ,hfree⟩ := h (n+1) (Nat.succ_pos n) hbeta
      let d : ℝ := min δ ((beta (n+1)-7/8)/2)
      have hd : 0<d := lt_min hδ (by linarith)
      have hdδ : d≤δ := min_le_left _ _
      have hdb : d≤(beta (n+1)-7/8)/2 := min_le_right _ _
      refine ⟨d,hd,?_⟩
      intro χ s hn hs hpole hz
      by_cases hsmall : χ.k.natAbs≤n
      · have hb := (zero_re_le_beta n χ hsmall hs hpole hz).trans ih
        linarith
      · have habs : χ.k.natAbs=n+1 := by omega
        have hk0 : χ.k≠0 := by
          intro he
          simp [he] at habs
        have hnegative (ψ : AngularCharacter) (hk : ψ.k= -((n+1:ℕ):ℤ))
            (z : ℂ) (hz : FamilyContinuation.LFunction ψ z=0) :
            z.re≤beta (n+1)-δ := le_of_not_gt (fun hb=>hfree ψ hk z hb hz)
        rcases Int.natAbs_eq_iff.mp habs with hk|hk
        · have hkc : χ.conjugate.k= -((n+1:ℕ):ℤ) := by
            rw [AngularCharacter.conjugate_k,hk]
          have hzc : FamilyContinuation.LFunction χ.conjugate (starRingEnd ℂ s)=0 := by
            rw [FamilyConjugation.LFunction_conjugate χ hk0,Complex.conj_conj,hz,map_zero]
          have hb := hnegative χ.conjugate hkc (starRingEnd ℂ s) hzc
          simp only [Complex.conj_re] at hb
          linarith
        · have hb := hnegative χ hk s hz
          linarith

theorem nonzero_of_negative_order_improvement (h : NegativeOrderImprovement)
    (χ : AngularCharacter) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hpole : χ.k=0 → χ.residue=1 → s≠1) : FamilyContinuation.LFunction χ s≠0 :=
  LFunction_ne_zero_of_beta_lt χ.k.natAbs χ (le_refl _)
    ((beta_le_of_negative_order_improvement h χ.k.natAbs).trans_lt hs) hpole

end OAI.SevenEighths.Angular.PhysicalCapClosure
#print axioms OAI.SevenEighths.Angular.PhysicalCapClosure.typeZero_nonzero
#print axioms OAI.SevenEighths.Angular.PhysicalCapClosure.beta_zero_le
#print axioms OAI.SevenEighths.Angular.PhysicalCapClosure.beta_le_of_negative_order_improvement
#print axioms OAI.SevenEighths.Angular.PhysicalCapClosure.nonzero_of_negative_order_improvement
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalCapClosure.nonzero_of_negative_order_improvement
