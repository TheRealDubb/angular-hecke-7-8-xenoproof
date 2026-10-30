import AngularInactiveEnergy
import OAI.NumberTheory.DirichletL.Reflection.CanonicalFrozenEnergyUniformDegree

/-! The angular inactive physical source and its frozen-label aggregation.
AngularMixedReflection already includes the derivative normalization; this
statement deliberately has no additional outer inverse derivative scalar.
All finite source costs and harmonic losses are paid explicitly. -/
namespace OAI.CubicEisenstein.AngularFrozenEnergy
open scoped Classical BigOperators ContDiff
open SevenEighths ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
open InverseReflectedPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
section
variable (order : ℕ)
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (FF : φ→Ideal Eis) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (lists : σ→Finset (Ideal Eis)) (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) (T : Finset σ)

def angularInactivePhysical
    (D : OriginalSplitCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G FF rows hrows lists hmax hgood T)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) (K : rows) : ℂ :=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
        (∏ i : T,w i.val (p.val i))*AngularMixedReflection.angularMixedReflected order (D K b p) s
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K.val) T) W X
end

theorem angular_canonical_frozen_energy (order : ℕ)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ), ∀ {Nlevel : Eis}, ∀
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (_hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (_hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (_hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (_hB : B≠0),
    ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm J:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
    Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J (B*F*R) Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J (B*F*R) Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J (B*F*R) Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J (B*F*R) Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (poolPrimeFamily J (B*F*R) Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
          ∑ T : Finset σ,angularInactivePhysical order
            ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (poolPrimeFamily J (B*F*R) Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/16-O₀/2) := by
  obtain ⟨degree,hu⟩ := AngularInactiveEnergy.angular_canonical_inactive_energy order lo hi hlo W hWs hW L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,?_⟩
  intro Nlevel γ _ a c₀ mode _ s hc₀ hNlevel hbase hac B hB
  obtain ⟨C,Z₁,hC,hZ₁,he⟩ := hu a c₀ mode s hc₀ hNlevel hbase hac B hB
  let ε := cstar/(32*(4*L+2))
  have hε : 0<ε := div_pos hcstar (by positivity)
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (Ideal.absNorm B:ℝ)
  refine ⟨Cb*C,Z₀,by positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F R Q₀ hJ hF hR Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1 : Z₁≤Z := (le_max_left _ _).trans hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₁ hz1
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  have hall := fun (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) =>
    he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
      hz1 hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
      parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
      (fun f => hGN f.val) (fun f => hGchar f.val)
      (fun K hK => ⟨fun f => (hrowcop K hK).1 f.val,(hrowcop K hK).2⟩) hLN hLchar T
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) (K : rows) =>
    angularInactivePhysical order ((poolPrimeFamily J (B*F*R) Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K
  have hs (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) :
      (∑ K : rows,‖source g A T K‖^2)≤harm*energy := by
    apply (hD g A T θ w hw).trans
    apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact subtype_product_le_full (fun i => i∉T) (fun i => 256*(columnDyadicLength (H i)+1:ℝ)) (fun i => by have hn : (0:ℝ)≤columnDyadicLength (H i) := Nat.cast_nonneg _; linarith)
  let Labels := γ×(Finset (FreeReflection.pool J (B*F*R) Q₀)×Finset σ)
  let f := fun (b : Labels) (K : rows) => (scalar b.1 K*frozenInactiveWeight J F (B*F*R) Q₀ b.2.1)*source b.1 b.2.1 b.2.2 K
  have hf (b : Labels) : (∑ K : rows,‖f b K‖^2)≤harm*energy := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK => ?_)).trans (hs b.1 b.2.1 b.2.2)
    rw [norm_mul]
    exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F (B*F*R) Q₀ b.2.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfam := weighted_finite_row_energy_uniform (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
    (fun _ => (1:ℂ)) f (harm*energy) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (K : rows) : (∑ b : Labels,f b K)=∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
        ∑ T : Finset σ,source g A T K := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hsource : (∑ K : rows,‖∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
        ∑ T : Finset σ,source g A T K‖^2)≤
      (Fintype.card Labels:ℝ)^2*harm*energy := by
    simp_rw [←hid]
    exact hfam.trans_eq (by ring)
  apply hsource.trans
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_max_right _ _).trans hZ
  have hmaskn := canonical_mask_norm_cap B F R Z V L L hz.le hBn hFn hRn hVc (le_refl _)
  have hJn' : (Ideal.absNorm J:ℝ)≤Z^L := hJn.trans (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
  have hpool : (Ideal.absNorm (J*(B*F*R)):ℝ)≤Z^(3*L+1) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^L*Z^(2*L+1) := mul_le_mul hJn' hmaskn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by rw [←Real.rpow_add hzp];congr 1;ring
  have hbudget : ε*((3*L+1)+L)≤cstar/32 := by
    have heq : ε*(4*L+2)=cstar/32 := by dsimp [ε];field_simp
    have hh := mul_le_mul_of_nonneg_left (show (3*L+1)+L≤4*L+2 by linarith) hε.le
    rwa [heq] at hh
  have hcst := hcost H hcard hH1 J (B*F*R) Q₀ hJ (mul_ne_zero (mul_ne_zero hB hF) hR)
    Z (3*L+1) L (cstar/32) hz hpool
    (hprod.trans (Real.rpow_le_rpow_of_exponent_le hz.le hzc)) hbudget
  calc
    _ = ((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (Cb*Z^(cstar/32))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
      exact hcst
    _ = (Cb*C)*(1+‖θ‖)^degree*
        Z^(cstar/32+(N+V-cstar/8-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)

#print axioms angular_canonical_frozen_energy
end
end OAI.CubicEisenstein.AngularFrozenEnergy
