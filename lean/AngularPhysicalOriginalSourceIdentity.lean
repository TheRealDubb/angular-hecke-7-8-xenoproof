import AngularPhysicalPlainCommonSource
import AngularPhysicalPlainInductionEnergy
import OAI.NumberTheory.DirichletL.Energy.OriginalSource

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.CommonRows
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentRetainedProfile
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentPositiveSummability (bounded_radial_summable)
open CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [instι:Fintype ι] [decι:DecidableEq ι]
local instance angularOriginalSourceDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def volume (s:Input ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem volume_pos (s:Input ι) : 0<volume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

def coefficient (s:Input ι) (R seed:Ideal O) : Ideal O→ℂ :=
  finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)

def completeInput (s : Data ι) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hν : ∀i I,‖s.ν i I‖≤1) (hW : ∀i x,‖s.W i x‖≤s.M i)
    (lo hi : ℝ) (hlo : 0<lo) (hl : ∀i,lo≤s.lo i) (hh : ∀i,s.hi i≤hi) : Input ι where
  toData := s
  plain₁ := plainSupportPool s.b₁ s.X₁ s.Y₁
  plain₂ := plainSupportPool s.b₂ s.X₂ s.Y₂
  plain₁_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  plain₂_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  coverage₁ := plainSupportPool_coverage s.W₁ s.b₁ s.X₁ s.Y₁ hz₁ s.support₁ s.X₁_pos s.Y₁_pos
  coverage₂ := plainSupportPool_coverage s.W₂ s.b₂ s.X₂ s.Y₂ hz₂ s.support₂ s.X₂_pos s.Y₂_pos
  ν_bound := hν
  W_bound := hW
  lower := lo
  upper := hi
  lower_pos := hlo
  lower_le := hl
  upper_ge := hh

omit [DecidableEq ι] in
lemma input_tuplePool (s : Input ι) :
    Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
  ext v
  simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]

lemma input_polynomial_difference (s : Input ι) (R : Ideal O) (z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I)=
    (rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.X₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.X₂-
     rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.Y₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.Y₂)*
        ∏i,rowSlot s.η (fixedBadMask*idealGenerator R) 1 z (s.slots i)
          (s.toData.coefficient i) s.t := by
  unfold coefficient
  rw [input_tuplePool]
  rw [source_polynomial_eq_maskedRectangle s.η fixedBadMask 1 z s.t
    (dvd_mul_right _ _) (dvd_mul_left _ _) s.slots s.plain₁ s.plain₂ R 1
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 s.coverage₁ s.coverage₂]
  simp only [map_one,Nat.cast_one,div_one,maskedRectangle,one_dvd,ite_true,one_mul]
  exact actual_slot_rectangle_sum s.η (fixedBadMask*idealGenerator R) 1 z s.slots
    s.toData.coefficient s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos

lemma normalized_input_difference (s : Input ι) (R : Ideal O) (z : O) :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.X₁ s.X₂-
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (volume s):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I := by
  rw [input_polynomial_difference]
  unfold positiveSlotRow volume
  rw [s.same_product]
  ring


end OAI.SevenEighths.Angular.PlainRows.CommonRows

#print axioms OAI.SevenEighths.Angular.PlainRows.CommonRows.normalized_input_difference
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.CommonRows.normalized_input_difference
