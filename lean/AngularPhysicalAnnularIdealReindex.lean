import AngularPhysicalAnnularFourierLattice
import AngularPhysicalPlainOutside

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.AnnularReflection
open EisensteinSchwartzPoisson ConcreteTraceCRT ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => ActualEisensteinCubic.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem radial_ideal_reindex (η:AngularCharacter) (W:ℝ→ℂ) (X:ℝ)
    (hs:Summable (fun z:O=>η.elementCoeff z*W (‖eisEmbedding z‖^2/X))) :
    (∑'z:O,η.elementCoeff z*W (‖eisEmbedding z‖^2/X))=
      6*∑'I:NI,η.idealHom I.val*W ((I.val.absNorm:ℝ)/X) := by
  rw [UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (fun z:O=>η.elementCoeff z*W (‖eisEmbedding z‖^2/X)) hs
    (by rw [η.elementCoeff_zero,zero_mul])
    (fun u z=>by rw [η.elementCoeff_unit_mul,norm_eisEmbedding_unit_mul])]
  congr 1
  apply tsum_congr
  intro I
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,span_idealGenerator]
  rw [←η.idealHom_of_generator (span_idealGenerator I.val)]

theorem bounded_radial_summable (η:AngularCharacter) (W:ℝ→ℂ) (X:ℝ)
    (hs:Summable (fun z:O=>‖W (‖eisEmbedding z‖^2/X)‖)) :
    Summable (fun z:O=>η.elementCoeff z*W (‖eisEmbedding z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (η.norm_elementCoeff_le_one z)

theorem original_radial_summable (η:AngularCharacter) (W:𝓢(ℝ,ℂ)) (X:ℝ) (hX:0<X) :
    Summable (fun z:O=>η.elementCoeff z*W (‖eisEmbedding z‖^2/X)) := by
  apply bounded_radial_summable
  simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)

theorem reflected_radial_summable (η:AngularCharacter) (k:ℤ) (a b:ℝ) (ha:0<a)
    (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (X:ℝ) (hX:0<X) :
    Summable (fun z:O=>η.elementCoeff z*AnnularFourier.profile k a b ha W (‖eisEmbedding z‖^2/X)) :=
  bounded_radial_summable η _ X (AnnularFourier.profile_lattice_summable k a b ha W hs X hX)

end OAI.SevenEighths.Angular.AnnularReflection

#print axioms OAI.SevenEighths.Angular.AnnularReflection.radial_ideal_reindex
#print axioms OAI.SevenEighths.Angular.AnnularReflection.reflected_radial_summable
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AnnularReflection.reflected_radial_summable
