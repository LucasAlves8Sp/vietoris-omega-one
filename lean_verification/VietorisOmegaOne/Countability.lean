import VietorisOmegaOne.TopologyProof

noncomputable section
open Set TopologicalSpace
namespace VietorisOmegaOne

local instance : Countable X := inferInstanceAs (Countable (Option ℕ))

theorem finite_of_compact_no_infty {s : Set X} (hc : IsCompact s)
    (hi : OnePoint.infty ∉ s) : s.Finite := by
  have hopen (n : ℕ) : IsOpen ({(n : X)} : Set X) := by
    simpa using (OnePoint.isOpen_image_coe (s := ({n} : Set ℕ))).mpr (isOpen_discrete _)
  obtain ⟨F, hF⟩ := hc.elim_finite_subcover
    (fun n : ℕ => ({(n : X)} : Set X)) hopen (by
      intro x hx
      cases x with
      | none => exact (hi hx).elim
      | some n => exact Set.mem_iUnion.mpr ⟨n, Set.mem_singleton_iff.mpr rfl⟩)
  refine F.finite_toSet.image (fun n : ℕ => (n : X)) |>.subset ?_
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hF hx)
  obtain ⟨hnF, hxn⟩ := Set.mem_iUnion.mp hn
  exact ⟨n, hnF, Set.mem_singleton_iff.mp hxn |>.symm⟩

theorem cofinite_of_open_infty {U : Set X} (ho : IsOpen U)
    (hi : OnePoint.infty ∈ U) : Uᶜ.Finite :=
  finite_of_compact_no_infty ho.isClosed_compl.isCompact (by simpa using hi)

def smallOpen : Set (Set X) := {U | IsOpen U ∧ (U.Finite ∨ Uᶜ.Finite)}

theorem countable_smallOpen : smallOpen.Countable := by
  have hf : {U : Set X | U.Finite}.Countable := Set.Countable.setOf_finite
  have hc : {U : Set X | Uᶜ.Finite}.Countable := by
    have he : {U : Set X | Uᶜ.Finite} = (fun V : Set X => Vᶜ) '' {U : Set X | U.Finite} := by
      ext U
      constructor
      · intro h; exact ⟨Uᶜ, h, compl_compl U⟩
      · rintro ⟨V, hV, rfl⟩; simpa using hV
    rw [he]
    exact hf.image _
  exact (hf.union hc).mono fun U h => h.2

def subgenerators : Set (Set K) :=
  (fun U : Set X => {f : K | Set.range f.val ⊆ U}) '' smallOpen ∪
    ⋃ i : ℕ, (fun U : Set X => {f : K | f.val i ∈ U}) '' smallOpen

def smallTopology : TopologicalSpace K := generateFrom subgenerators

theorem countable_subgenerators : subgenerators.Countable :=
  (countable_smallOpen.image _).union (Set.countable_iUnion fun _ => countable_smallOpen.image _)

theorem small_open_tube {U : Set X} (hU : U ∈ smallOpen) :
    @IsOpen K smallTopology {f : K | Set.range f.val ⊆ U} := by
  exact isOpen_generateFrom_of_mem (Or.inl ⟨U, hU, rfl⟩)

theorem small_open_coordinate (i : ℕ) {U : Set X} (hU : U ∈ smallOpen) :
    @IsOpen K smallTopology {f : K | f.val i ∈ U} := by
  exact isOpen_generateFrom_of_mem (Or.inr (Set.mem_iUnion.mpr ⟨i, U, hU, rfl⟩))

theorem small_open_any_tube {U : Set X} (ho : IsOpen U) :
    @IsOpen K smallTopology {f : K | Set.range f.val ⊆ U} := by
  by_cases hi : OnePoint.infty ∈ U
  · exact small_open_tube ⟨ho, Or.inr (cofinite_of_open_infty ho hi)⟩
  · letI : TopologicalSpace K := smallTopology
    apply isOpen_iff_mem_nhds.mpr
    intro f hf
    have hno : OnePoint.infty ∉ Set.range f.val := fun h => hi (hf h)
    have hfin := finite_of_compact_no_infty f.property hno
    have hopen : IsOpen (Set.range f.val) :=
      (OnePoint.isOpen_iff_of_not_mem hno).mpr (isOpen_discrete _)
    have hself : Set.range f.val ⊆ Set.range f.val := subset_rfl
    exact Filter.mem_of_superset ((small_open_tube ⟨hopen, Or.inl hfin⟩).mem_nhds hself)
      (fun g hg => by
        change Set.range g.val ⊆ U
        exact hg.trans hf)

theorem small_open_any_coordinate (i : ℕ) {U : Set X} (ho : IsOpen U) :
    @IsOpen K smallTopology {f : K | f.val i ∈ U} := by
  by_cases hi : OnePoint.infty ∈ U
  · exact small_open_coordinate i ⟨ho, Or.inr (cofinite_of_open_infty ho hi)⟩
  · letI : TopologicalSpace K := smallTopology
    apply isOpen_iff_mem_nhds.mpr
    intro f hf
    have hno : OnePoint.infty ∉ ({f.val i} : Set X) := by
      intro h; exact hi ((Set.mem_singleton_iff.mp h).symm ▸ hf)
    have hopen : IsOpen ({f.val i} : Set X) :=
      (OnePoint.isOpen_iff_of_not_mem hno).mpr (isOpen_discrete _)
    exact Filter.mem_of_superset ((small_open_coordinate i
      ⟨hopen, Or.inl (Set.finite_singleton _)⟩).mem_nhds rfl)
      (fun g hg => by
        have heq : g.val i = f.val i := Set.mem_singleton_iff.mp hg
        change g.val i ∈ U
        rw [heq]
        exact hf)

theorem topology_eq_small : kTopology = smallTopology := by
  apply le_antisymm
  · apply le_generateFrom
    intro A hA
    rcases hA with hA | hA
    · obtain ⟨U, hU, rfl⟩ := hA
      exact open_tube U hU.1
    · obtain ⟨i, U, hU, rfl⟩ := Set.mem_iUnion.mp hA
      exact open_coordinate i U hU.1
  · change smallTopology ≤ TopologicalSpace.induced (fun f : K => f.val) powerTopology
    letI : TopologicalSpace K := smallTopology
    apply le_induced_generateFrom
    rintro A ⟨U, F, V, hU, hV, rfl⟩
    have he : (fun f : K => f.val) ⁻¹' basic U F V =
        {f : K | Set.range f.val ⊆ U} ∩ ⋂ i ∈ F, {f : K | f.val i ∈ V i} := by
      ext f; simp [basic]
    rw [he]
    exact (small_open_any_tube hU).inter
      (isOpen_biInter_finset fun i hi => small_open_any_coordinate i (hV i hi))

theorem second_countable : SecondCountableTopology K := by
  rw [topology_eq_small]
  exact SecondCountableTopology.mk' countable_subgenerators

theorem main_theorem : MainClaim := by
  letI := second_countable
  exact ⟨second_countable, isLindelof_univ, not_sigmaCompact⟩

end VietorisOmegaOne
