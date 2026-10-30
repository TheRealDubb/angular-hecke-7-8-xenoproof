import AngularPhysicalAnnularFourierHeight
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularFourier
open FourierBridge EisensteinSchwartzPoisson

theorem absolute_order_source_separation (angularOrder:ℕ) (a b:ℝ) (ha:0<a)
    (V:ℝ→ℂ) (M:ℝ) (hM:0≤M) (hV:∀y,V y≠0 → |y|≤M) (A J:ℕ) :
    ∃H:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder →
      ∀G:𝓢(ℝ,ℂ),∀D:ℝ,0<D → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤D →
      ∀s:ℝ,0<s → ∃density:𝓢(ℝ,ℂ),
        (∀y:ℝ,V y*profile k a b ha G (s*Real.exp y)=
          ∫v:ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v:ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v:ℝ,(1+‖v‖)^J*‖density v‖)≤C*D ∧
        (∀v:ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*D) := by
  obtain ⟨C,hC,hsep⟩:=LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _:Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨H,K,hK,hEuler⟩:=absolute_order_euler_bound angularOrder a b ha
    A (J+(volume:Measure ℝ).integrablePower)
  refine ⟨H,(C+1)*K,by positivity,?_⟩
  intro k hk G D hD hGD s hs
  obtain ⟨density,hid,hi,hm,hp⟩:=hsep (profile k a b ha G)
    (profile_contDiffOn k a b ha G) (K*D) (by positivity)
    (fun j hj x hx=>(hEuler k hk G j hj x hx.le).trans
      (mul_le_mul_of_nonneg_left hGD hK.le)) s hs
  have hconst:C*(K*D)≤((C+1)*K)*D:=by nlinarith [mul_pos hK hD]
  exact ⟨density,(fun y=>by simpa using hid (fun _:Unit=>y)),hi,
    hm.trans hconst,fun v=>(hp v).trans hconst⟩

theorem absolute_order_profile_separation (angularOrder:ℕ) (a b:ℝ) (ha:0<a)
    (V:ℝ→ℂ) (M:ℝ) (hM:0≤M) (hV:∀y,V y≠0 → |y|≤M) (A J:ℕ) :
    ∃n:ℕ,∀W:ℝ→ℂ,∀hs:Function.support W⊆Set.Icc a b,∀hW:ContDiff ℝ ∞ W,
      ∃C:ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀t s:ℝ,0<s →
      ∃density:𝓢(ℝ,ℂ),
        (∀y:ℝ,V y*profile k a b ha
          (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) (s*Real.exp y)=
          ∫v:ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v:ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v:ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v:ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨C,hC,hsep⟩:=LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _:Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨n,hn⟩:=absolute_order_height_control angularOrder a b ha
    A (J+(volume:Measure ℝ).integrablePower)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩:=hn W hs hW
  refine ⟨(C+1)*D,by positivity,?_⟩
  intro k hk t s hs0
  obtain ⟨density,hid,hi,hm,hp⟩:=hsep _ (profile_contDiffOn k a b ha _)
    (D*(1+‖t‖)^n) (by positivity) (fun j hj x hx=>hDb k hk t j hj x hx.le) s hs0
  refine ⟨density,?_,hi,hm.trans ?_,fun v=>(hp v).trans ?_⟩
  · intro y
    simpa using hid (fun _:Unit=>y)
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]

end OAI.SevenEighths.Angular.AnnularFourier

#print axioms OAI.SevenEighths.Angular.AnnularFourier.absolute_order_source_separation
#print axioms OAI.SevenEighths.Angular.AnnularFourier.absolute_order_profile_separation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularFourier.absolute_order_profile_separation
