import AngularPhysicalFirstSourceCaps
import AngularPhysicalFirstPhysicalDyadic
import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
universe u
namespace OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open PlainRows PlainRows.CommonRows PlainRows.FirstPhysical
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalDyadicAssembly (Blocks effectiveScale retainedIndices mem_retainedIndices)
open CenteredMomentSecondRetainedAggregate (commonLabels_supported)
open CenteredMomentSecondBlockAggregate (ActiveLabel)
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstExtractedLedger
open CenteredMomentEnergyFirstAnnularAdmission (amplifierCap)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance successorSourceGeometryDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _
abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (PlainRows.CommonRows.coefficient s R seed)

def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (PlainRows.CommonRows.volume s)) Z ξ

abbrev SourceBlocks (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (PlainRows.CommonRows.coefficient s R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (PlainRows.CommonRows.coefficient s R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (PlainRows.CommonRows.coefficient s R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s R seed K Z ξ p E) 1) W (fun _=>logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤hi i)(hb₁:|s.b₁|≤b₁)(hb₂:|s.b₂|≤b₂)
    (hZ:1≤Z)(hfixed:(∏i,hi i)*b₁*b₂≤Z)
    (hV:PlainRows.CommonRows.volume s≤Z^B):sourceRadius s≤Z^(B+1) := by
  have hVol:0<PlainRows.CommonRows.volume s:=PlainRows.CommonRows.volume_pos s
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*PlainRows.CommonRows.volume s:=by
    unfold PlainRows.CommonRows.sourceRadius PlainRows.CommonRows.volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>hhi i)
  have hb₁0:0≤b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

omit [DecidableEq ι] in
lemma source_dyad_retained (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Retained (localRadius s R seed K Z ξ p E) (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  exact ((mem_retainedIndices _ _).mp hn).1

omit [DecidableEq ι] in
lemma source_dyad_gt_one (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):1<dyadicScale (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  obtain ⟨q,hq,hweight⟩:=((mem_retainedIndices _ _).mp hn).2
  exact hq.trans_lt ((dyadicWeight_support (n 1)) hweight).2

omit [DecidableEq ι] in
lemma source_nominal_positive (s:Input ι)(R seed:Ideal O)(K:ℝ)(hK:0<K)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    0<firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (PlainRows.CommonRows.volume s):=by
  have he:=Ideal.span_singleton_eq_bot.not.mpr
    (primeSubsetGenerator_ne_zero (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using he
  exact firstNominalScale_pos _ _ _ hE K _ hK (PlainRows.CommonRows.volume_pos s)

omit [DecidableEq ι] in
lemma source_nominal_span (s:Input ι)(R seed:Ideal O)(K:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (PlainRows.CommonRows.volume s)=
      firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (PlainRows.CommonRows.volume s):=by rw [primeSubsetGenerator,span_idealGenerator]

omit [DecidableEq ι] in
theorem source_amplifier_packet (A D ξcap Z:ℝ)(hZ:32≤Z)
    (s:Input ι)(R seed:Ideal O)(K ξ:ℝ)(hK:0<K)(hξ:ξ≤ξcap)
    (hV:PlainRows.CommonRows.volume s≤Z^A)(hKi:K⁻¹≤Z^D)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (PlainRows.CommonRows.volume s);
    0<Tsec ∧ 0<dyadicScale (n 1) ∧
      dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
      8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
      Tsec≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (PlainRows.CommonRows.volume s):=by
  have hz:1≤Z:=by linarith
  have hzpos:0<Z:=by linarith
  have hfreq:=retained_scale_le _ (n 1) (source_dyad_retained s R seed K Z ξ p E n)
  have hV':PlainRows.CommonRows.volume s≤Z^(max A D):=hV.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _))
  have hKi':K⁻¹≤Z^(max A D):=hKi.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _))
  have hrad:=local_frequency_radius_cap p.val.1 p.val.2 E K (PlainRows.CommonRows.volume s) Z
    (max A D) ξ hK (PlainRows.CommonRows.volume_pos s).le hz hV' hKi'
  have hrad':localRadius s R seed K Z ξ p E≤Z^(3*max A D+ξcap/2):=by
    apply hrad.trans
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  refine ⟨source_nominal_positive s R seed K hK p E,dyadicScale_pos _,hfreq,?_,?_⟩
  · calc
      _≤32*Z^(3*max A D+ξcap/2):=by linarith
      _≤Z*Z^(3*max A D+ξcap/2):=
        mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hzpos.le _)
      _=Z^(amplifierCap A D ξcap):=by
        unfold amplifierCap
        rw [Real.rpow_add_one hzpos.ne']
        ring
  · rw [one_mul]
    exact (source_nominal_span s R seed K p E).le

omit [DecidableEq ι] in
lemma source_frequency_ledger (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(hK:0<K)(hZ:1<Z)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (PlainRows.CommonRows.volume s))+
        frequencyLoss Z 1 ξ:=by
  apply retained_first_dyad_enclosure _ Z 1 _ ξ hZ (by norm_num) _ (n 1)
    (source_dyad_retained s R seed K Z ξ p E n)
  rw [one_mul,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (source_nominal_positive s R seed K hK p E)]

theorem fixed_endpoint_radius (N:ℕ)(upper b₁ b₂ A Z:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂)(hZ:32≤Z)
    (hfixed:upper^N*b₁*b₂≤Z)
    (s:Input ι)(hN:Fintype.card ι≤N)
    (hhi:∀i,|s.hi i|≤upper)(hs₁:|s.b₁|≤b₁)(hs₂:|s.b₂|≤b₂)
    (hV:PlainRows.CommonRows.volume s≤Z^A):sourceRadius s≤Z^(A+1):=by
  apply input_radius_cap (fun _:ι=>upper) b₁ b₂ A Z s hhi hs₁ hs₂ (by linarith) _ hV
  have hpow:upper^(Fintype.card ι)≤upper^N:=pow_le_pow_right₀ hu hN
  simpa only [Finset.prod_const,Finset.card_univ] using
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hb₁) hb₂).trans hfixed

theorem eventually_source_admission (N:ℕ)(upper b₁ b₂ A D ξcap:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(α:Type u)[Fintype α][DecidableEq α],∀s:Input α,Fintype.card α≤N →
      (∀i,|s.hi i|≤upper) → |s.b₁|≤b₁ → |s.b₂|≤b₂ →
      ∀(R seed:Ideal O)(K ξ:ℝ),0<K → ξ≤ξcap →
      PlainRows.CommonRows.volume s≤Z^A → K⁻¹≤Z^D →
      sourceRadius s≤Z^(A+1) ∧
      ∀(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
        (n:SourceBlocks s R seed K Z ξ p E),
      let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (PlainRows.CommonRows.volume s);
      0<Tsec ∧ 1<dyadicScale (n 1) ∧
        dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
        8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
        Tsec≤1*firstNominalScale p.val.1 p.val.2
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
          K (PlainRows.CommonRows.volume s):=by
  filter_upwards [eventually_ge_atTop (32:ℝ),eventually_ge_atTop (upper^N*b₁*b₂)] with Z hZ hf
  refine ⟨by linarith,?_⟩
  intro α _ _ s hN hhi hs₁ hs₂ R seed K ξ hK hξ hV hKi
  refine ⟨fixed_endpoint_radius N upper b₁ b₂ A Z hu hb₁ hb₂ hZ hf s hN hhi hs₁ hs₂ hV,?_⟩
  intro p E n
  have hh:=source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi p E n
  exact ⟨hh.1,source_dyad_gt_one s R seed K Z ξ p E n,hh.2.2⟩


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.input_radius_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.input_radius_cap

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_dyad_retained
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_dyad_retained

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_dyad_gt_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_dyad_gt_one

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_nominal_positive
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_nominal_positive

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_nominal_span
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_nominal_span

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_amplifier_packet
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_amplifier_packet

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_frequency_ledger
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.source_frequency_ledger

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.fixed_endpoint_radius
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.fixed_endpoint_radius

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.eventually_source_admission
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.eventually_source_admission
