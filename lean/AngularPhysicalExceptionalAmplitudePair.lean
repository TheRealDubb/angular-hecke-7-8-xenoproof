import AngularPhysicalExceptionalAmplitudeData

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ExceptionalAmplitudePair
open PlainRows DetectorAmplitude ExceptionalShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open CenteredMomentExceptionalAmplitudePair (Tests norm_le_of_squared)
local notation "O" => ActualEisensteinCubic.O
universe u
theorem actual_paired_amplitude (angularType:ℤ) (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r:ℝ),s.η.k=angularType → v.η.k=angularType → 1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B r z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨J,hJ⟩:=actual_allocated_amplitude angularType ε B hε hB
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩:=hJ Q hQ
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι κ _ _ _ _ s v p q Z r hstype hvtype hZ z hs hv D a b
  have hpoint (α:Type u) [Fintype α] [DecidableEq α] (s:Data α)(p:Tests) (htype:s.η.k=angularType)
      (hs:Admissible s p Q Z B r z)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))):
      ‖amplitude s D a z‖≤C*Z^ε*p.heightWeight s.t^J*slotControl s*Real.sqrt (volume s)/
        (formalReductionFactor D a s.P*Z^(max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)):=by
    obtain ⟨hP,hm,hA,hz,hml,hm2,hcond,hex,hW₁,hW₂,hX₁,hX₂,hY₁,hY₂⟩:=hs
    apply norm_le_of_squared _ _ _ _ _
    · exact mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg s)
    · exact (volume_pos s).le
    · exact s.reduction_pos D a
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hbound α s Z htype hZ hP z hm hA hz hml hm2 hcond hex D a
        (p.reverse 0) (p.reverse 1) (p.index 0) (p.index 1) (p.index_le 0) (p.index_le 1)
        (p.sigma 0) (p.sigma_mem 0) (p.sigma 1) (p.sigma_mem 1)
        (p.height 0) (p.height 1) r hW₁ hW₂ hX₁ hX₂ hY₁ hY₂
  have hl:=hpoint ι s p hstype hs a
  have hr:=hpoint κ v q hvtype hv b
  have hcap:1≤Z^(max (r-Real.logb Z (formalReductionFactor D b v.P)) 0):=
    Real.one_le_rpow hZ.le (le_max_right _ _)
  have hr':‖amplitude v D b z‖≤
      C*Z^ε*q.heightWeight v.t^J*slotControl v*Real.sqrt (volume v)/formalReductionFactor D b v.P:=by
    apply hr.trans
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity) (slotControl_nonneg v)) (Real.sqrt_nonneg _))
      (v.reduction_pos D b)
    exact le_mul_of_one_le_right (v.reduction_pos D b).le hcap
  apply (mul_le_mul hl hr' (norm_nonneg _) (by
    exact div_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
      (slotControl_nonneg s)) (Real.sqrt_nonneg _)) (mul_nonneg (s.reduction_pos D a).le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))).trans_eq
  rw [←reduction_cap_identity s v D a b Z r hZ]
  have hp:Z^(2*ε)=(Z^ε)^2:=by rw [mul_comm (2:ℝ) ε,Real.rpow_mul (zero_lt_one.trans hZ).le,Real.rpow_two]
  rw [hp]
  ring

end OAI.SevenEighths.Angular.ExceptionalAmplitudePair

#print axioms OAI.SevenEighths.Angular.ExceptionalAmplitudePair.actual_paired_amplitude
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalAmplitudePair.actual_paired_amplitude
