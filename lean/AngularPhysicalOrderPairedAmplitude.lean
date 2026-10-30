import AngularPhysicalExceptionalAmplitudePair

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ExceptionalAmplitudePair
open PlainRows DetectorAmplitude ExceptionalShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDetectorDictionary ConcretePrimeRowBridge
open CenteredMomentExceptionalAmplitudePair (Tests norm_le_of_squared)
local notation "O" => ActualEisensteinCubic.O
universe u
theorem actual_order_paired_amplitude (angularOrder:ℕ) (ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Tests)(Z r:ℝ),s.η.k.natAbs=angularOrder → v.η.k=s.η.k → 1<Z → ∀z:O,
      Admissible s p Q Z B r z → Admissible v q Q Z B r z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*Z^(2*ε)*p.heightWeight s.t^J*q.heightWeight v.t^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r:=by
  obtain ⟨Jp,hJp⟩ := actual_paired_amplitude (angularOrder:ℤ) ε B hε hB
  obtain ⟨Jn,hJn⟩ := actual_paired_amplitude (-(angularOrder:ℤ)) ε B hε hB
  refine ⟨max Jp Jn,?_⟩
  intro Q hQ
  obtain ⟨Cp,hCp,hplus⟩ := hJp Q hQ
  obtain ⟨Cn,hCn,hminus⟩ := hJn Q hQ
  refine ⟨Cp+Cn,by positivity,?_⟩
  intro ι κ _ _ _ _ s v p q Z r horder htype hZ z hs hv D a b
  have ht₁ : 1≤p.heightWeight s.t := by
    dsimp only [Tests.heightWeight]
    linarith only [norm_nonneg (p.height 0),norm_nonneg (p.height 1),norm_nonneg s.t]
  have ht₂ : 1≤q.heightWeight v.t := by
    dsimp only [Tests.heightWeight]
    linarith only [norm_nonneg (q.height 0),norm_nonneg (q.height 1),norm_nonneg v.t]
  have hs0 := slotControl_nonneg s
  have hv0 := slotControl_nonneg v
  have hw0 : 0≤exceptionalWeight s.toSource v.toSource D a b Z r :=
    Real.rpow_nonneg (zero_le_one.trans hZ.le) _
  have hg (c:ℝ) (j:ℕ) (hc:0<c) (hcC:c≤Cp+Cn) (hj:j≤max Jp Jn) :
      c*Z^(2*ε)*p.heightWeight s.t^j*q.heightWeight v.t^j*
        slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
          exceptionalWeight s.toSource v.toSource D a b Z r ≤
      (Cp+Cn)*Z^(2*ε)*p.heightWeight s.t^(max Jp Jn)*q.heightWeight v.t^(max Jp Jn)*
        slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
          exceptionalWeight s.toSource v.toSource D a b Z r := by
    gcongr <;> assumption
  have hsign : s.η.k=(angularOrder:ℤ) ∨ s.η.k=-(angularOrder:ℤ) := by
    have habs : |s.η.k|=(angularOrder:ℤ) := by
      simpa only [Int.natCast_natAbs] using congrArg (fun n:ℕ=>(n:ℤ)) horder
    rcases le_total 0 s.η.k with hk | hk
    · exact Or.inl (by simpa only [abs_of_nonneg hk] using habs)
    · right
      rw [abs_of_nonpos hk] at habs
      linarith
  rcases hsign with hk | hk
  · exact (hplus ι κ s v p q Z r hk (htype.trans hk) hZ z hs hv D a b).trans
      (hg Cp Jp hCp (le_add_of_nonneg_right hCn.le) (le_max_left _ _))
  · exact (hminus ι κ s v p q Z r hk (htype.trans hk) hZ z hs hv D a b).trans
      (hg Cn Jn hCn (le_add_of_nonneg_left hCp.le) (le_max_right _ _))
end OAI.SevenEighths.Angular.ExceptionalAmplitudePair

#print axioms OAI.SevenEighths.Angular.ExceptionalAmplitudePair.actual_order_paired_amplitude
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalAmplitudePair.actual_order_paired_amplitude
