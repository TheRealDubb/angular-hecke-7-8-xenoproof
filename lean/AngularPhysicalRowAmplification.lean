import AngularPhysicalPrimeEnergy

noncomputable section
open scoped Classical ContDiff
namespace OAI.SevenEighths.Angular.InverseRows
open OAI.SevenEighths.Angular.Dyadic InverseAmplification
theorem RowData.prime_column (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    polynomial (data.character u) true W D σ freq=
      polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq-
      (data.character u).idealHom P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq :=
  prime_column_identity _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

theorem RowData.prime_energy (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD


#print axioms RowData.prime_column
#print axioms RowData.prime_energy
end OAI.SevenEighths.Angular.InverseRows
