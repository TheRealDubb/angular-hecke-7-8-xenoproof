import AngularPhysicalAnnularPairEnergy
import OAI.NumberTheory.DirichletL.Moments.ReflectedUniformPair

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace OAI.SevenEighths.Angular.AnnularEnergy
open FourierBridge AnnularFourier
open CenteredMomentReflectedProfileMeasure (logWindow row_density_energy)
open CenteredMomentReflectedUniformPair (normalized_density_bound envelope envelope_pos
  envelope_integrable envelope_integral heightScale)

theorem actual_one_uniform (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [instι:Fintype ι],∀k:ι→ℤ,(∀i,(k i).natAbs=angularOrder) →
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→AngularCharacter)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖Dyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖Dyadic.polynomial (χ i) false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*profile (k i) a b ha (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,K,hK,hb⟩ := absolute_order_source_separation angularOrder a b ha V M hM hV A (J+2)
  refine ⟨H,(K*Real.pi)^2,by positivity,?_⟩
  intro ι _ k hk G χ P s X hs hX D E hD hE hGD henergy
  choose d hid hi hm hp using fun i=>hb (k i) (hk i) (G i) D hD (hGD i) (s i) (hs i)
  let e (i : ι) : ℂ := (1+s i)^A
  let F (i : ι) (x : ℝ) := e i*profile (k i) a b ha (G i) x
  let φ (i : ι) (v : ℝ) := Dyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : Dyadic.polynomial (χ i) false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*profile (k i) a b ha (G i) (s i*x))
        (X i) 0 0*P i=∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : (fun x=>logWindow V x*((1+s i)^A:ℂ)*profile (k i) a b ha (G i) (s i*x))=
        (fun x=>logWindow V x*F i (s i*x)) := by funext x;dsimp [F,e];ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (P i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hpoint (i : ι) : ∀v,‖(e i • d i) v‖≤envelope (K*D) J v := by
    have hh := normalized_density_bound A 0 J (s i) 0 (K*D) (hs i) (d i)
      (by simpa using hp i)
    simpa [heightScale,e] using hh
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope (K*D) J)
    (fun v=>(1+‖v‖)^J) (envelope_pos (K*D) (mul_pos hK hD) J)
    (by intro v;positivity) hpoint hint (envelope_integrable (K*D) J) E hE henergy
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  convert hh using 1
  ring


end OAI.SevenEighths.Angular.AnnularEnergy

#print axioms OAI.SevenEighths.Angular.AnnularEnergy.actual_one_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularEnergy.actual_one_uniform
