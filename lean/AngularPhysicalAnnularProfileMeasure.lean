import AngularPhysicalFiniteAnnularSeparation
import AngularPhysicalAnnularFourierSeparation

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularEnergy
open FourierBridge AnnularFourier
open CenteredMomentReflectedProfileMeasure (logWindow logWindow_support row_density_energy row_density_energy_two)
local notation "O" => ActualEisensteinCubic.O

theorem plain_annular_separation (V F : ℝ→ℂ) (M s X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v) (η : AngularCharacter) :
    Dyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*Dyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  exact finite_annular_separation V F s X hX density hsep η S hs hc

theorem actual_plain_profile_measure (angularOrder:ℕ) (a b:ℝ) (ha:0<a)
    (V:ℝ→ℂ) (M:ℝ) (hM:0≤M) (hV:∀y,V y≠0 → |y|≤M) (A J:ℕ) :
    ∃n:ℕ,∀W:ℝ→ℂ,∀hs:Function.support W⊆Set.Icc a b,∀hW:ContDiff ℝ ∞ W,
      ∃C:ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀t s:ℝ,0<s →
      ∃density:𝓢(ℝ,ℂ),
        (∀(η:AngularCharacter)(X:ℝ),0<X →
          Dyadic.polynomial η false (fun x=>logWindow V x*profile k a b ha
            (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) (s*x)) X 0 0=
          ∫v:ℝ,density v*Dyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
        Integrable (fun v:ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v:ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v:ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨n,hn⟩:=absolute_order_profile_separation angularOrder a b ha V M hM hV A J
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hn W hs hW
  refine ⟨C,hC,?_⟩
  intro k hk t s hs0
  obtain ⟨density,hsep,hi,hm,hp⟩:=hb k hk t s hs0
  exact ⟨density,(fun η X hX=>plain_annular_separation V _ M s X hX hV density hsep η),hi,hm,hp⟩

end OAI.SevenEighths.Angular.AnnularEnergy

#print axioms OAI.SevenEighths.Angular.AnnularEnergy.actual_plain_profile_measure
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularEnergy.actual_plain_profile_measure
