import AngularPhysicalExceptionalProfileMass

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalSourceShell
open PlainRows DetectorAmplitude ExceptionalAmplitudePair ExceptionalShell
open CenteredMomentExceptionalAmplitudePair (Tests)
local notation "O" => ActualEisensteinCubic.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]
theorem actual_paired_source_shell (angularOrder:ℕ) (ε δ B:ℝ) (hε:0<ε) (hδ:0<δ) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests)(Z r:ℝ),s.η.k.natAbs=angularOrder → v.η.k=s.η.k → 1<Z →
      ∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T:ℝ,1≤T →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*(2*T)^(2*δ)*Z^(2*ε+v.toSource.allowance Z-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_order_paired_amplitude angularOrder ε B hε hB
  obtain ⟨Cs,hCs,hshell⟩:=uniform_subset_shell (ι:=ι) δ hδ
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨Ca,hCa,hpoint⟩:=hJ Q hQ
  refine ⟨Ca*Cs,mul_pos hCa hCs,?_⟩
  intro I L s v p q Z r horder htype hZ rows hs hv Ds hD T hT hlo hhi
  have hz:0<Z:=zero_lt_one.trans hZ
  let A:=Ca*Z^(2*ε)*profileMass s v p q J
  have hA:0≤A:=mul_nonneg (mul_nonneg hCa.le (Real.rpow_nonneg hz.le _)) (profileMass_nonneg s v p q J)
  have hp (D:Ideal O)(a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (I⊕Fin 2)))
      (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (L⊕Fin 2))):
      (∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        (rows.card:ℝ)*A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
    calc
      _≤∑z∈rows,A*exceptionalWeight s.toSource v.toSource D a b Z r:=by
        apply Finset.sum_le_sum
        intro z hzrow
        exact (hpoint I L s v p q Z r horder htype hZ z (hs z hzrow) (hv z hzrow) D a b).trans_eq (by
          dsimp only [A,profileMass]
          ring)
      _=_:=by simp; ring
  have hsum:=hshell I L s.toSource v.toSource Ds hD T Z r hT hZ hlo hhi
  calc
    _≤∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        (rows.card:ℝ)*A*exceptionalWeight s.toSource v.toSource D a b Z r:=
      Finset.sum_le_sum (fun D _=>Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hp D a b)))
    _=(rows.card:ℝ)*A*(∑D∈Ds,∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        exceptionalWeight s.toSource v.toSource D a b Z r):=by simp only [Finset.mul_sum]
    _≤(rows.card:ℝ)*A*(Cs*(2*T)^(2*δ)*Z^(v.toSource.allowance Z-r)):=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg _) hA)
    _=_:=by
      rw [show 2*ε+v.toSource.allowance Z-r=2*ε+(v.toSource.allowance Z-r) by ring,Real.rpow_add hz]
      dsimp only [A]
      ring

end OAI.SevenEighths.Angular.ExceptionalSourceShell

#print axioms OAI.SevenEighths.Angular.ExceptionalSourceShell.actual_paired_source_shell
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalSourceShell.actual_paired_source_shell
