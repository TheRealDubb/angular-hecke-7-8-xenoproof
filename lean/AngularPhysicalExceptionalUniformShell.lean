import AngularPhysicalExceptionalShell

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalShell
open PlainRows CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorBoundary CenteredMomentSlotRatios
open CenteredMomentExceptionalAllocationShell (exact_max_cancellation)
open CenteredMomentUniformDivisorShell (numerical_allowance)
local notation "O" => ActualEisensteinCubic.O
theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

def ShellBound (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε : ℝ) : Prop := ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r)

theorem uniform_subset_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (hε : 0<ε) : ∃C : ℝ,0<C ∧ ∀J L : Finset ι,ShellBound J L C ε := by
  have he (p : Finset ι×Finset ι) : ∃C : ℝ,0<C ∧ ShellBound p.1 p.2 C ε :=
    actual_exceptional_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B : ℝ := 1+∑p : Finset ι×Finset ι,C p
  have hs : 0≤∑p : Finset ι×Finset ι,C p := Finset.sum_nonneg (fun p _=>(hC p).le)
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro J L s v Ds hD T Z r hT hZ hlo hhi
  have hc : C (J,L)≤B := by
    have hp := Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]; linarith
  exact (hbound (J,L) s v Ds hD T Z r hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem exceptional_shell_subpower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι→ℝ) (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(J L : Finset ι) (s : Source J) (v : Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,
      1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r) := by
  let ε : ℝ := δ/(2*(B+1))
  have hε : 0<ε := div_pos hδ (by positivity)
  have he : 2*B*ε≤δ := by
    have hh : ε*(2*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := uniform_subset_shell (ι:=ι) ε hε
  let E : ℝ := Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E]; positivity,?_⟩
  intro J L s v hvlo hvhi Ds hD T Z r hT hZ hTZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hbound J L s v Ds hD T Z r hT hZ hlo hhi
  have hv : Z^(v.allowance Z-r)≤E*Z^(-r) := by
    calc
      _≤Z^((∑i,logWindow (lo i) (hi i))/Real.log Z-r) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le
          (sub_le_sub_right (subset_allowance L v lo hi hvlo hvhi Z hZ) r)
      _=E*Z^(-r) := by rw [sub_eq_add_neg,Real.rpow_add hz,numerical_allowance Z _ hZ]
  have hpow : T^(2*ε)≤Z^δ := by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith [he])
  apply hh.trans
  calc
    _≤C*(2*T)^(2*ε)*(E*Z^(-r)) := mul_le_mul_of_nonneg_left hv (by positivity)
    _=(C*2^(2*ε)*E)*T^(2*ε)*Z^(-r) := by
      rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) ht.le]; ring
    _≤(C*2^(2*ε)*E)*Z^δ*Z^(-r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [E]; positivity)) (by positivity)
    _=(C*2^(2*ε)*E)*Z^(δ-r) := by rw [mul_assoc,←Real.rpow_add hz]; rfl

end OAI.SevenEighths.Angular.ExceptionalShell

#print axioms OAI.SevenEighths.Angular.ExceptionalShell.subset_allowance
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalShell.subset_allowance

#print axioms OAI.SevenEighths.Angular.ExceptionalShell.uniform_subset_shell
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalShell.uniform_subset_shell

#print axioms OAI.SevenEighths.Angular.ExceptionalShell.exceptional_shell_subpower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalShell.exceptional_shell_subpower
