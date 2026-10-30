import AngularPhysicalExceptionalWeight

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalShell
open PlainRows CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorBoundary CenteredMomentSlotRatios
open CenteredMomentExceptionalAllocationShell (exact_max_cancellation)
open CenteredMomentUniformDivisorShell (numerical_allowance)
local notation "O" => ActualEisensteinCubic.O
theorem actual_exceptional_shell {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (hι : Fintype.card ι≤N) (hκ : Fintype.card κ≤N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by
  obtain ⟨C₁,hC₁,hcard₁⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z r hT hZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc₁ (D : Ideal O) (hd : D∈Ds) : ((s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D : Ideal O) (hd : D∈Ds) : ((v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D : Ideal O) (hd : D∈Ds) :
      (∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤
        (C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := by
    have hn : (0:ℝ)<Ideal.absNorm D := ht.trans_le (hlo D hd)
    have he : (Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε) := by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow : (Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε) :=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _ ≤ ∑_a∈s.active D,∑_b∈v.active D,Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) :=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>
          active_exceptional_weight s v D (hD D hd) a b ha hb Z r hZ))
      _ = ((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by simp; ring
      _ ≤ (C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*
          (Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _ = (C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
        (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _ ≤ ∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := Finset.sum_le_sum hp
    _ = (Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) := by simp
    _ ≤ (256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) :=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _ = (256*C₁*C₂)*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by field_simp

end OAI.SevenEighths.Angular.ExceptionalShell

#print axioms OAI.SevenEighths.Angular.ExceptionalShell.actual_exceptional_shell
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalShell.actual_exceptional_shell
