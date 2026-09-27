import VietorisOmegaOne.Model
import VietorisOmegaOne.Diagonal

noncomputable section
open Set TopologicalSpace
namespace VietorisOmegaOne

theorem open_basic (U : Set X) (F : Finset ℕ) (V : ℕ → Set X)
    (hU : IsOpen U) (hV : ∀ i ∈ F, IsOpen (V i)) :
    IsOpen {f : K | f.val ∈ basic U F V} := by
  letI : TopologicalSpace RawSequence := powerTopology
  exact isOpen_induced (isOpen_generateFrom_of_mem ⟨U, F, V, hU, hV, rfl⟩)

theorem open_tube (U : Set X) (hU : IsOpen U) :
    IsOpen {f : K | Set.range f.val ⊆ U} := by
  simpa [basic] using open_basic U ∅ (fun _ => Set.univ) hU (by simp)

theorem open_coordinate (i : ℕ) (U : Set X) (hU : IsOpen U) :
    IsOpen {f : K | f.val i ∈ U} := by
  simpa [basic] using open_basic Set.univ {i} (fun _ => U) isOpen_univ
    (by intros; exact hU)

theorem continuous_coordinate (i : ℕ) : Continuous (fun f : K => f.val i) := by
  exact continuous_def.mpr fun U hU => open_coordinate i U hU

theorem closed_surjections : IsClosed surjectionSet := by
  have hhit (x : X) : IsClosed {f : K | x ∈ Set.range f.val} := by
    have ho := open_tube ({x}ᶜ) isClosed_singleton.isOpen_compl
    have he : {f : K | Set.range f.val ⊆ {x}ᶜ} = {f : K | x ∈ Set.range f.val}ᶜ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.subset_def,
        Set.mem_singleton_iff]
      constructor
      · intro h hx; exact h x hx rfl
      · intro h y hy hyx; exact h (hyx ▸ hy)
    rw [he] at ho
    exact isOpen_compl_iff.mp ho
  have he : surjectionSet = {f : K | f.val 0 = OnePoint.infty} ∩
      ⋂ x : X, {f : K | x ∈ Set.range f.val} := by
    ext f
    simp [surjectionSet, Function.Surjective]
  rw [he]
  exact (isClosed_singleton.preimage (continuous_coordinate 0)).inter
    (isClosed_iInter hhit)

theorem compact_occurrence_bound (C : Set K) (hc : IsCompact C)
    (hs : C ⊆ surjectionSet) (n : ℕ) :
    ∃ b : ℕ, ∀ f ∈ C, ∃ k ≤ b, f.val k = (n : X) := by
  have hopen (k : ℕ) : IsOpen {f : K | f.val k = (n : X)} := by
    change IsOpen ((fun f : K => f.val k) ⁻¹' ({(n : X)} : Set X))
    have hs : IsOpen ({(n : X)} : Set X) := by
      simpa using (OnePoint.isOpen_image_coe (s := ({n} : Set ℕ))).mpr (isOpen_discrete _)
    exact (continuous_coordinate k).isOpen_preimage _ hs
  obtain ⟨J, hJ⟩ := hc.elim_finite_subcover
    (fun k => {f : K | f.val k = (n : X)}) hopen (by
      intro f hf
      obtain ⟨k, hk⟩ := (hs hf).2 (n : X)
      exact Set.mem_iUnion.mpr ⟨k, hk⟩)
  refine ⟨J.sup id, ?_⟩
  intro f hf
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hJ hf)
  obtain ⟨hkJ, he⟩ := Set.mem_iUnion.mp hk
  exact ⟨k, Finset.le_sup (f := id) hkJ, he⟩

theorem not_sigmaCompact : ¬ IsSigmaCompact (Set.univ : Set K) := by
  intro h
  obtain ⟨C, hc, hcover⟩ := h.of_isClosed_subset closed_surjections (Set.subset_univ _)
  have hsub (n : ℕ) : C n ⊆ surjectionSet := by
    rw [← hcover]
    exact Set.subset_iUnion C n
  choose b hb using fun n => compact_occurrence_bound (C n) (hc n) (hsub n) n
  let g : K := ⟨Diagonal.delayedSequence b, by
    rw [Set.range_eq_univ.mpr (Diagonal.surjective b)]
    exact isCompact_univ⟩
  have hg : g ∈ surjectionSet := ⟨Diagonal.at_zero b, Diagonal.surjective b⟩
  rw [← hcover] at hg
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
  obtain ⟨k, hk, he⟩ := hb n g hn
  have hlate := Diagonal.hit_after_bound b he
  exact (Nat.not_lt_of_ge hk) hlate

end VietorisOmegaOne
