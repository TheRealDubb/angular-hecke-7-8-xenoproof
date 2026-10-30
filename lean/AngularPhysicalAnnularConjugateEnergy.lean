import AngularPhysicalAnnularOneEnergy
import AngularPhysicalConjugation

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularEnergy
open FourierBridge AnnularFourier
open CenteredMomentReflectedProfileMeasure (logWindow row_density_energy)
open CenteredMomentReflectedUniformPair (normalized_density_bound envelope envelope_pos
  envelope_integrable envelope_integral heightScale)

lemma conjugate_annular_frequency (χ:AngularCharacter) (V:ℝ→ℂ)
    (hreal:∀y,conj (V y)=V y) (X v:ℝ) (hX:0<X) :
    Dyadic.polynomial χ.conjugate false (logWindow V) X 0 (2*Real.pi*v)=
      conj (Dyadic.polynomial χ false (logWindow V) X 0 (-2*Real.pi*v)) := by
  have hr:(fun x=>conj (logWindow V x))=logWindow V:=by
    funext x
    unfold logWindow
    split_ifs <;> simp [hreal]
  have hf:-(-2*Real.pi*v)=2*Real.pi*v:=by ring
  simpa only [hr,hf] using
    (InverseAmplification.conj_polynomial χ false (logWindow V) X 0 (-2*Real.pi*v) hX).symm

theorem actual_inverse_uniform (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [instι:Fintype ι],∀k:ι→ℤ,(∀i,(k i).natAbs=angularOrder) →
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→AngularCharacter)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖Dyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖Dyadic.polynomial (χ i).conjugate false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*profile (k i) a b ha (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,C,hC,hbound⟩ := actual_one_uniform angularOrder a b ha V M hM hV A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ k hk G χ P s X hs hX D E hD hE hGD henergy
  apply hbound k hk G (fun i=>(χ i).conjugate) P s X hs hX D E hD hE hGD
  intro v
  have he (i : ι) :
      ‖Dyadic.polynomial (χ i).conjugate false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖=
      ‖Dyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖ := by
    rw [conjugate_annular_frequency (χ i) V hreal (X i) v (hX i),norm_mul,
      Complex.norm_conj,←norm_mul]
  simpa only [he] using henergy v


end OAI.SevenEighths.Angular.AnnularEnergy

#print axioms OAI.SevenEighths.Angular.AnnularEnergy.actual_inverse_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularEnergy.actual_inverse_uniform
