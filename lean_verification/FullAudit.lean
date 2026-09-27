import VietorisOmegaOne.OrderResult

/-
A successful build of the library alone is not verification of the paper.
This audit requires the exact unconditional topological conclusion. The
main_theorem declaration must be checked together with the model definitions.

After completing it, run this file and inspect the transitive axiom output.
Do not accept sorryAx, a user axiom, Lean.ofReduceBool, or an assumed main lemma
as a certificate of the mathematical result. Standard classical Lean axioms
must be disclosed rather than described as 'no axioms'.
-/

example : VietorisOmegaOne.MainClaim := VietorisOmegaOne.main_theorem

#print VietorisOmegaOne.main_theorem
#print VietorisOmegaOne.MainClaim
#print VietorisOmegaOne.K
#print VietorisOmegaOne.powerTopology
#print axioms VietorisOmegaOne.main_theorem
#check VietorisOmegaOne.orderModelHomeomorph
#print axioms VietorisOmegaOne.orderModelHomeomorph

example : VietorisOmegaOne.CompactPowerClaim ℕ∞ := VietorisOmegaOne.order_model_theorem
#print VietorisOmegaOne.CompactPowerClaim
#print VietorisOmegaOne.CompactPower
#print VietorisOmegaOne.compactPowerTopology
#print axioms VietorisOmegaOne.order_model_theorem
