import AngularPhysicalReciprocalRegular

/- Supremum of actual zeros over all finite conductors and a fixed finite
range of signed angular types. Only the absolute half-plane Re(s)>1 is used
to prove boundedness. No seed or proposed 7/8 theorem is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
open Set Complex
namespace OAI.SevenEighths.Angular.PhysicalZeroSupremum

def zeroRealParts (n : ℕ) : Set ℝ :=
  {x | ∃(χ : AngularCharacter)(s : ℂ),χ.k.natAbs≤n ∧ 0<s.re ∧
    (χ.k=0 → χ.residue=1 → s≠1) ∧ FamilyContinuation.LFunction χ s=0 ∧ s.re=x}

def zeroSet (n : ℕ) : Set ℝ := insert (1/2) (zeroRealParts n)

def beta (n : ℕ) : ℝ := sSup (zeroSet n)

theorem zeroRealParts_le_one (n : ℕ) {x : ℝ} (hx : x∈zeroRealParts n) : x≤1 := by
  obtain ⟨χ,s,_,_,_,hz,rfl⟩ := hx
  by_contra hn
  exact FamilyContinuation.LFunction_ne_zero χ s (lt_of_not_ge hn) hz

theorem zeroSet_bddAbove (n : ℕ) : BddAbove (zeroSet n) := by
  refine ⟨1,?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl|hx
  · norm_num
  · exact zeroRealParts_le_one n hx

theorem zeroSet_nonempty (n : ℕ) : (zeroSet n).Nonempty := Set.insert_nonempty _ _

theorem half_le_beta (n : ℕ) : (1/2:ℝ)≤beta n :=
  le_csSup (zeroSet_bddAbove n) (Set.mem_insert _ _)

theorem beta_le_one (n : ℕ) : beta n≤1 := by
  apply csSup_le (zeroSet_nonempty n)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl|hx
  · norm_num
  · exact zeroRealParts_le_one n hx

theorem zero_re_le_beta (n : ℕ) (χ : AngularCharacter) (hn : χ.k.natAbs≤n)
    {s : ℂ} (hs : 0<s.re) (hpole : χ.k=0 → χ.residue=1 → s≠1)
    (hz : FamilyContinuation.LFunction χ s=0) : s.re≤beta n :=
  le_csSup (zeroSet_bddAbove n) (Set.mem_insert_of_mem _ ⟨χ,s,hn,hs,hpole,hz,rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (n : ℕ) (χ : AngularCharacter)
    (hn : χ.k.natAbs≤n) {s : ℂ} (hs : beta n<s.re)
    (hpole : χ.k=0 → χ.residue=1 → s≠1) :
    FamilyContinuation.LFunction χ s≠0 := by
  intro hz
  have hpos : 0<s.re := by linarith [half_le_beta n]
  exact (not_lt_of_ge (zero_re_le_beta n χ hn hpos hpole hz)) hs

theorem regular_ne_zero_of_beta_lt (n : ℕ) (χ : AngularCharacter)
    (hn : χ.k.natAbs≤n) {s : ℂ} (hs : beta n<s.re) :
    PhysicalLogarithmicInput.regular χ s≠0 := by
  have hpos : 0<s.re := by linarith [half_le_beta n]
  by_cases hp : χ.k=0 ∧ χ.residue=1
  · by_cases h1 : s=1
    · subst s
      exact PhysicalLogarithmicInput.regular_principal_one_ne_zero χ hp.1 hp.2
    · rw [PhysicalLogarithmicInput.regular_eq_principal_factor χ hp.1 hp.2 hpos h1]
      have hplus : s+1≠0 := by
        intro h
        have hr := congrArg Complex.re h
        simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
        linarith
      exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1)
        (LFunction_ne_zero_of_beta_lt n χ hn hs (fun _ _=>h1))) hplus
  · have hnp : χ.k≠0 ∨ χ.residue≠1 := by tauto
    rw [PhysicalLogarithmicInput.regular_eq_nonprincipal χ hnp]
    exact LFunction_ne_zero_of_beta_lt n χ hn hs (fun hk hr=>False.elim (hp ⟨hk,hr⟩))

theorem reciprocal_differentiableAt_of_beta_lt (n : ℕ) (χ : AngularCharacter)
    (hn : χ.k.natAbs≤n) {s : ℂ} (hs : beta n<s.re) :
    DifferentiableAt ℂ (PhysicalReciprocal.reciprocal χ) s :=
  PhysicalReciprocal.reciprocal_differentiableAt_of_regular_ne_zero χ
    (by linarith [half_le_beta n]) (regular_ne_zero_of_beta_lt n χ hn hs)

/-- A numerical seed remains a separate explicit supplier. This lemma alone
does not establish any improved zero-free half-plane. -/
theorem beta_le_of_half_plane (n : ℕ) (b : ℝ) (hb : 1/2≤b)
    (hfree : ∀(χ : AngularCharacter)(s : ℂ),χ.k.natAbs≤n → b<s.re →
      (χ.k=0 → χ.residue=1 → s≠1) → FamilyContinuation.LFunction χ s≠0) :
    beta n≤b := by
  apply csSup_le (zeroSet_nonempty n)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl|hx
  · exact hb
  · obtain ⟨χ,s,hn,_,hpole,hz,rfl⟩ := hx
    by_contra h
    exact hfree χ s hn (lt_of_not_ge h) hpole hz

theorem beta_le_of_uniform_improvement (n : ℕ) (b : ℝ) (hb : 1/2≤b)
    (hbound : b<beta n → ∃δ : ℝ,0<δ ∧
      ∀(χ : AngularCharacter)(s : ℂ),χ.k.natAbs≤n → 0<s.re →
      (χ.k=0 → χ.residue=1 → s≠1) →
      FamilyContinuation.LFunction χ s=0 → s.re≤beta n-δ) : beta n≤b := by
  by_contra h
  have hbeta : b<beta n := lt_of_not_ge h
  obtain ⟨δ,hδ,hzeros⟩ := hbound hbeta
  have hupper : beta n≤max (1/2) (beta n-δ) := by
    apply csSup_le (zeroSet_nonempty n)
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl|hx
    · exact le_max_left _ _
    · obtain ⟨χ,s,hn,hs,hpole,hz,rfl⟩ := hx
      exact (hzeros χ s hn hs hpole hz).trans (le_max_right _ _)
  have hlt : max (1/2:ℝ) (beta n-δ)<beta n :=
    max_lt (hb.trans_lt hbeta) (sub_lt_self _ hδ)
  exact (not_lt_of_ge hupper) hlt

end OAI.SevenEighths.Angular.PhysicalZeroSupremum
#print axioms OAI.SevenEighths.Angular.PhysicalZeroSupremum.LFunction_ne_zero_of_beta_lt
#print axioms OAI.SevenEighths.Angular.PhysicalZeroSupremum.regular_ne_zero_of_beta_lt
#print axioms OAI.SevenEighths.Angular.PhysicalZeroSupremum.reciprocal_differentiableAt_of_beta_lt
#print axioms OAI.SevenEighths.Angular.PhysicalZeroSupremum.beta_le_of_half_plane
#print axioms OAI.SevenEighths.Angular.PhysicalZeroSupremum.beta_le_of_uniform_improvement
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalZeroSupremum.beta_le_of_uniform_improvement
