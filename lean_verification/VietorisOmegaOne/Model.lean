import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete

/-!
# Model and statement of the intended theorem

The model for the ordinal omega + 1 is the one-point compactification
of the discrete natural numbers. OrderModel.lean identifies it with the
order topology on the extended natural numbers. The main proof is in
Countability.lean. See verification-status.json for the actual check status.

The topology on K below is the Vietoris-power subspace topology. In particular,
we do NOT silently use the ordinary product topology on the whole space K.

Reference: Caruvana--Holshouser, arXiv:2507.17936v3, Definitions 1.8 and 1.14,
pp. 4--5, and Question 1, p. 11.
-/

noncomputable section

namespace VietorisOmegaOne

abbrev X := OnePoint ℕ
abbrev RawSequence := ℕ → X

/-- Basic sets in the full Vietoris power. -/
def basic (U : Set X) (F : Finset ℕ) (V : ℕ → Set X) :
    Set RawSequence :=
  {f | Set.range f ⊆ U ∧ ∀ i ∈ F, f i ∈ V i}

/-- The source's range bound and finitely many coordinate bounds are open. -/
def generators : Set (Set RawSequence) :=
  {A | ∃ (U : Set X) (F : Finset ℕ) (V : ℕ → Set X),
    IsOpen U ∧ (∀ i ∈ F, IsOpen (V i)) ∧ A = basic U F V}

def powerTopology : TopologicalSpace RawSequence :=
  TopologicalSpace.generateFrom generators

/-- We use actual compactness, not an assumed compact-range characterization. -/
def K := {f : RawSequence // IsCompact (Set.range f)}

instance kTopology : TopologicalSpace K :=
  TopologicalSpace.induced (fun f : K => f.val) powerTopology

/-- Exact target in the one-point-compactification model. -/
def MainClaim : Prop :=
  SecondCountableTopology K ∧
    IsLindelof (Set.univ : Set K) ∧
    ¬ IsSigmaCompact (Set.univ : Set K)

/-- The closed-surjection subspace used in the paper. -/
def surjectionSet : Set K :=
  {f | f.val 0 = (OnePoint.infty : X) ∧ Function.Surjective f.val}

-- Countability.lean supplies main_theorem; FullAudit.lean checks its axioms.

end VietorisOmegaOne
