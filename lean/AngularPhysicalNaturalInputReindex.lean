import AngularPhysicalZeroPhysicalSign
import AngularPhysicalOriginalColumnSupport
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalInputReindex
open PlainRows PlainRows.CommonRows
open CanonicalQuadraticSieve CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O"=>ActualEisensteinCubic.O
variable {α β:Type*}[Fintype α][Fintype β]
local instance successorInputReindexDecEq {κ:Type*}:DecidableEq κ:=Classical.decEq _
local instance successorInputReindexSumLeft : DecidableEq (α⊕Fin 2):=Classical.decEq _
local instance successorInputReindexSumRight : DecidableEq (β⊕Fin 2):=Classical.decEq _
def reindex (e : α≃β) (s : Input α) : Input β where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i=>s.slots (e.symm i)
  prime := fun i=>s.prime (e.symm i)
  ν := fun i=>s.ν (e.symm i)
  W := fun i=>s.W (e.symm i)
  lo := fun i=>s.lo (e.symm i)
  hi := fun i=>s.hi (e.symm i)
  P := fun i=>s.P (e.symm i)
  lo_pos := fun i=>s.lo_pos (e.symm i)
  P_pos := fun i=>s.P_pos (e.symm i)
  support := fun i=>s.support (e.symm i)
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i=>s.M (e.symm i)
  M_ge_one := fun i=>s.M_ge_one (e.symm i)
  coefficient_bound := fun i=>s.coefficient_bound (e.symm i)
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i=>s.ν_bound (e.symm i)
  W_bound := fun i=>s.W_bound (e.symm i)
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le (e.symm i)
  upper_ge := fun i=>s.upper_ge (e.symm i)

def tupleMap (e : α≃β) : Tuple α≃Tuple β :=
  (e.sumCongr (Equiv.refl (Fin 2))).arrowCongr (Equiv.refl (Ideal O))

omit [Fintype α] [Fintype β] in
lemma tupleMap_apply (e : α≃β) (v : Tuple α) (j : β⊕Fin 2) :
    tupleMap e v j = v ((e.sumCongr (Equiv.refl (Fin 2))).symm j) := rfl

lemma tupleMap_product (e : α≃β) (v : Tuple α) :
    finiteTupleProduct (tupleMap e v)=finiteTupleProduct v :=
  (e.sumCongr (Equiv.refl (Fin 2))).symm.prod_comp v

lemma pools_map (e : α≃β) (s : Input α) :
    (Fintype.piFinset s.pools).image (tupleMap e) = Fintype.piFinset (reindex e s).pools := by
  ext v
  simp only [Finset.mem_image,Fintype.mem_piFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩ j
    cases j with
    | inl i => exact hw (Sum.inl (e.symm i))
    | inr i => exact hw (Sum.inr i)
  · intro hv
    refine ⟨(tupleMap e).symm v,?_,(tupleMap e).apply_symm_apply v⟩
    intro j
    cases j with
    | inl i => simpa [tupleMap,Input.pools,reindex] using hv (Sum.inl (e i))
    | inr i => exact hv (Sum.inr i)

lemma profile_map (e:α≃β)(s:Input α)(R seed:Ideal O)(v:Tuple α):
    profileCoefficient R (reindex e s).ν (reindex e s).W (reindex e s).P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed (tupleMap e v)=
    profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v:=by
  simp only [reindex,profileCoefficient,tupleMap_product,
    tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply,Sum.map_inl,Sum.map_inr]
  congr 3
  exact e.symm.prod_comp (fun i=>s.ν i (v (Sum.inl i))*
    s.W i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/s.P i))

lemma coefficient_map (e:α≃β)(s:Input α)(R seed:Ideal O):
    coefficient (reindex e s) R seed=coefficient s R seed:=by
  funext I
  unfold PlainRows.CommonRows.coefficient finiteColumnCoefficient
  change (∑v∈(Fintype.piFinset (reindex e s).pools).filter (fun v=>finiteTupleProduct v=I),
    profileCoefficient R (reindex e s).ν (reindex e s).W (reindex e s).P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v)=_
  rw [←pools_map e s,Finset.filter_image]
  rw [Finset.sum_image (fun v _ w _ h=>(tupleMap e).injective h)]
  simp only [tupleMap_product,profile_map]

lemma volume_map (e:α≃β)(s:Input α):volume (reindex e s)=volume s:=by
  simp only [PlainRows.CommonRows.volume,reindex,e.symm.prod_comp]

lemma sourceRadius_map (e:α≃β)(s:Input α):sourceRadius (reindex e s)=sourceRadius s:=by
  simp only [PlainRows.CommonRows.sourceRadius,reindex,e.symm.prod_comp]

end OAI.SevenEighths.Angular.NaturalInputReindex

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.tupleMap_apply
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.tupleMap_apply

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.tupleMap_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.tupleMap_product

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.pools_map
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.pools_map

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.profile_map
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.profile_map

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.coefficient_map
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.coefficient_map

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.volume_map
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.volume_map

#print axioms OAI.SevenEighths.Angular.NaturalInputReindex.sourceRadius_map
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalInputReindex.sourceRadius_map
