import AngularPhysicalAnnularConjugateEnergy

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace OAI.SevenEighths.Angular.NormalizedReflectionEnergy
open AnnularFourier
open AnnularEnergy (plain_annular_separation plain_density_integrable)
open CenteredMomentReflectedProfileMeasure (logWindow row_density_energy)
open CenteredMomentReflectedUniformPair (heightScale normalized_density_bound envelope
  envelope_pos envelope_integrable envelope_integral)

def normalizedReflected (k:ℤ) (V W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (A n:ℕ) (s t x:ℝ) : ℂ :=
  logWindow V x*(heightScale A n s t:ℂ)*
    profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) (s*x)

theorem actual_one_uniform (angularOrder:ℕ) (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀W:ℝ→ℂ,∀hs:Function.support W⊆Set.Icc a b,∀hW:ContDiff ℝ ∞ W,
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [instι:Fintype ι],∀k:ι→ℤ,(∀i,(k i).natAbs=angularOrder) → ∀(χ ψ : ι→AngularCharacter)(P : ι→ℂ)
        (s t X Y omega : ι→ℝ)(Wshort : ℝ→ℂ),
        (∀i,0<s i) → (∀i,0<X i) →
      ∀E : ℝ,0≤E →
      (∀v,(∑i,‖Dyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*
        Dyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖Dyadic.polynomial (χ i) false (normalizedReflected (k i) V W a b ha hs hW A n (s i) (t i)) (X i) 0 0 *
        Dyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤C*E := by
  obtain ⟨n,hn⟩ := absolute_order_profile_separation angularOrder a b ha V M hM hV A (J+2)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨(C*Real.pi)^2,by positivity,?_⟩
  intro ι _ k hk χ ψ P s t X Y omega Wshort hscale hX E hE henergy
  choose d hid hi hm hp using fun i=>hb (k i) (hk i) (t i) (s i) (hscale i)
  let e (i : ι) : ℂ := heightScale A n (s i) (t i)
  let F (i : ι) (x : ℝ) := e i*profile (k i) a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (t i)) x
  let Q (i : ι) := Dyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i
  let φ (i : ι) (v : ℝ) := Dyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*Q i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*FourierBridge.logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*FourierBridge.logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*FourierBridge.logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : Dyadic.polynomial (χ i) false
      (normalizedReflected (k i) V W a b ha hs hW A n (s i) (t i)) (X i) 0 0*Q i=
      ∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : normalizedReflected (k i) V W a b ha hs hW A n (s i) (t i)=
        (fun x=>logWindow V x*F i (s i*x)) := by
      funext x
      dsimp [normalizedReflected,F,e]
      ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (Q i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope C J)
    (fun v=>(1+‖v‖)^J) (envelope_pos C hC J) (by intro v;positivity)
    (fun i=>normalized_density_bound A n J (s i) (t i) C (hscale i) (d i) (hp i)) hint
    (envelope_integrable C J) E hE (by
      intro v
      simpa only [φ,Q,mul_assoc] using henergy v)
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  simpa only [Q,mul_assoc,mul_comm E] using hh


end OAI.SevenEighths.Angular.NormalizedReflectionEnergy

#print axioms OAI.SevenEighths.Angular.NormalizedReflectionEnergy.actual_one_uniform
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NormalizedReflectionEnergy.actual_one_uniform
