import AngularPhysicalProfileAmplitudePair

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.FiniteProfileExceptional
open PlainRows DetectorAmplitude ExceptionalShell ExceptionalAmplitudePair
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentFiniteProfileExceptional
open CenteredMomentExceptionalAmplitudePair (norm_le_of_squared)
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
universe u

lemma profile_control_mono {lo hi:ℝ} (p:Profiles lo hi)
    {S T:Finset (ℕ×ℕ)} (h:S⊆T) : p.control S≤p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem order_paired_amplitude_source_control (angularOrder:ℕ) (lo hi ε B:ℝ) (hlo:0<lo) (hhi:0≤hi) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃R:Finset (ℕ×ℕ),(0,0)∈R ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(ι κ:Type u) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ],
      ∀(s:Data ι)(v:Data κ)(p q:Profiles lo hi)(Z r rRight:ℝ),s.η.k.natAbs=angularOrder → v.η.k=s.η.k → 1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control R*q.control R*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z r := by
  obtain ⟨Jp,Rp,hRp,hJp⟩ := paired_amplitude_source_control (angularOrder:ℤ) lo hi ε B hlo hhi hε hB
  obtain ⟨Jn,Rn,hRn,hJn⟩ := paired_amplitude_source_control (-(angularOrder:ℤ)) lo hi ε B hlo hhi hε hB
  refine ⟨max Jp Jn,Rp∪Rn,Finset.mem_union.mpr (Or.inl hRp),?_⟩
  intro Q hQ
  obtain ⟨Cp,hCp,hplus⟩ := hJp Q hQ
  obtain ⟨Cn,hCn,hminus⟩ := hJn Q hQ
  refine ⟨Cp+Cn,by positivity,?_⟩
  intro ι κ _ _ _ _ s v p q Z r rRight horder htype hZ z hs hv D a b
  have ht₁ : 1≤1+‖s.t‖ := by linarith only [norm_nonneg s.t]
  have ht₂ : 1≤1+‖v.t‖ := by linarith only [norm_nonneg v.t]
  have hs0 := slotControl_nonneg s
  have hv0 := slotControl_nonneg v
  have hw0 : 0≤exceptionalWeight s.toSource v.toSource D a b Z r :=
    Real.rpow_nonneg (zero_le_one.trans hZ.le) _
  have hg (c:ℝ) (j:ℕ) (R':Finset (ℕ×ℕ)) (hR':R'⊆Rp∪Rn)
      (hc:0<c) (hcC:c≤Cp+Cn) (hj:j≤max Jp Jn) :
      c*p.control R'*q.control R'*Z^(2*ε)*(1+‖s.t‖)^j*(1+‖v.t‖)^j*
        slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
          exceptionalWeight s.toSource v.toSource D a b Z r ≤
      (Cp+Cn)*p.control (Rp∪Rn)*q.control (Rp∪Rn)*Z^(2*ε)*(1+‖s.t‖)^(max Jp Jn)*(1+‖v.t‖)^(max Jp Jn)*
        slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
          exceptionalWeight s.toSource v.toSource D a b Z r := by
    have hp := profile_control_mono p hR'
    have hq := profile_control_mono q hR'
    have hp0 := Profiles.control_nonneg p R'
    have hq0 := Profiles.control_nonneg q R'
    have hp1 := Profiles.control_nonneg p (Rp∪Rn)
    have hq1 := Profiles.control_nonneg q (Rp∪Rn)
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
  · exact (hplus ι κ s v p q Z r rRight hk (htype.trans hk) hZ z hs hv D a b).trans
      (hg Cp Jp Rp Finset.subset_union_left hCp (le_add_of_nonneg_right hCn.le) (le_max_left _ _))
  · exact (hminus ι κ s v p q Z r rRight hk (htype.trans hk) hZ z hs hv D a b).trans
      (hg Cn Jn Rn Finset.subset_union_right hCn (le_add_of_nonneg_left hCp.le) (le_max_right _ _))

end OAI.SevenEighths.Angular.FiniteProfileExceptional

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptional.profile_control_mono
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptional.profile_control_mono

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptional.order_paired_amplitude_source_control
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptional.order_paired_amplitude_source_control
