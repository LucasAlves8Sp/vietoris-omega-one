import VietorisOmegaOne.Model
import Mathlib.Topology.Instances.ENat

noncomputable section
open Filter Topology
namespace VietorisOmegaOne

/-- The natural numbers with a largest point, with their order topology,
are the ordinal omega + 1 model used here. -/
def toOrderModel : X → ℕ∞ := fun x => x

theorem continuous_toOrderModel : Continuous toOrderModel := by
  apply (OnePoint.continuous_iff_from_nat _).mpr
  apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
  intro n
  filter_upwards [Filter.eventually_gt_atTop n] with k hk
  change (n : ℕ∞) < (k : ℕ∞)
  exact_mod_cast hk

/-- Machine-checked identification with the order topology on N union {top}. -/
def orderModelHomeomorph : X ≃ₜ ℕ∞ :=
  (isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_toOrderModel, Function.bijective_id⟩).homeomorph toOrderModel

end VietorisOmegaOne
