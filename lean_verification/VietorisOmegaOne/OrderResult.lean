import VietorisOmegaOne.Countability
import VietorisOmegaOne.OrderModel

noncomputable section
namespace VietorisOmegaOne

/-- The source construction, now parameterized by its ground space. -/
def CompactPower (Y : Type) [TopologicalSpace Y] :=
  {f : ℕ → Y // IsCompact (Set.range f)}

def compactPowerTopology (Y : Type) [TopologicalSpace Y] :
    TopologicalSpace (CompactPower Y) :=
  TopologicalSpace.induced (fun f : CompactPower Y => f.val)
    (TopologicalSpace.generateFrom
      {A | ∃ (U : Set Y) (F : Finset ℕ) (V : ℕ → Set Y),
        IsOpen U ∧ (∀ i ∈ F, IsOpen (V i)) ∧
          A = {f : ℕ → Y | Set.range f ⊆ U ∧ ∀ i ∈ F, f i ∈ V i}})

def CompactPowerClaim (Y : Type) [TopologicalSpace Y] : Prop :=
  letI := compactPowerTopology Y
  SecondCountableTopology (CompactPower Y) ∧
    IsLindelof (Set.univ : Set (CompactPower Y)) ∧
    ¬ IsSigmaCompact (Set.univ : Set (CompactPower Y))

/-- The identity homeomorphism identifies the actual topology instances. -/
theorem base_topologies_equal :
    (inferInstance : TopologicalSpace X) =
      (inferInstance : TopologicalSpace ℕ∞) := by
  have h := orderModelHomeomorph.induced_eq
  change TopologicalSpace.induced (id : X → X)
    (inferInstance : TopologicalSpace ℕ∞) =
      (inferInstance : TopologicalSpace X) at h
  simpa only [induced_id] using h.symm

/-- Unconditional result for N with a greatest element, in its order topology.
No conclusion is assumed as a hypothesis. -/
theorem order_model_theorem : CompactPowerClaim ℕ∞ := by
  have h : CompactPowerClaim X := main_theorem
  change @CompactPowerClaim (Option ℕ)
    (inferInstance : TopologicalSpace X) at h
  change @CompactPowerClaim (Option ℕ)
    (inferInstance : TopologicalSpace ℕ∞)
  rw [← base_topologies_equal]
  exact h

end VietorisOmegaOne

-- Record the actual scope and transitive axioms at compilation time.
#print VietorisOmegaOne.CompactPowerClaim
#print VietorisOmegaOne.CompactPower
#print VietorisOmegaOne.compactPowerTopology
#print axioms VietorisOmegaOne.main_theorem
#print axioms VietorisOmegaOne.orderModelHomeomorph
#print axioms VietorisOmegaOne.order_model_theorem
