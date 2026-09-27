# On the Vietoris power of a convergent sequence

**Lucas Alves de Almeida** · lucasdeirva8x@gmail.com

The compact-range Vietoris power **K(omega + 1, ord)** is second-countable and Lindelof, but is not sigma-compact.

This repository contains the manuscript and a Lean 4 formalization addressing the omega + 1 case of Question 1, page 11, in Christopher Caruvana and Jared Holshouser, *An adaptation of the Vietoris topology for ordered compact sets*, [arXiv:2507.17936v3](https://arxiv.org/abs/2507.17936v3).

## Read the result

- [Article (PDF)](paper/paper.pdf)
- [Local Lean verification record (PDF)](paper/lean-verification-record.pdf)
- [Formalization and detailed reproduction instructions](lean_verification/README.md)
- [Final theorem for the order-topological model](lean_verification/VietorisOmegaOne/OrderResult.lean)
- [Compiler audit output](lean_verification/verification-audit.log)
- [Machine-readable verification status and source hashes](lean_verification/verification-status.json)

## Verification

The proof was checked locally with **Lean 4.19.0** and **mathlib v4.19.0**, pinned to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The final declaration is `VietorisOmegaOne.order_model_theorem`. It has no mathematical hypotheses. Its reported transitive axioms are `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, custom assumed mathematical result, or native-computation trust axiom occurs in the final theorem.

The formal carrier consists of sequences with genuinely compact image, and the topology is explicitly generated from the source's range and finite coordinate conditions. The entire construction is transferred to the extended natural numbers with their order topology, the concrete model of omega + 1.

With Lean installed, open PowerShell in `lean_verification`, download the pinned dependency caches if necessary, and run:

```powershell
lake exe cache get
.\verify.ps1
```

Keep the supplied dependency lockfile. The `lean_verification` directory preserves the verified source package and its hashes. The PDFs and this repository landing page are publication materials outside that source manifest.

This is a reproducible local verification record, not an institutional certificate, independent peer-review report, or priority claim. The correspondence with the arXiv definitions and indexing cardinal is explained in the article. Independent mathematical review and reproduction are welcome.

## AI disclosure

ChatGPT Astra performed almost all of the mathematical development, Lean formalization and manuscript preparation. Lucas Alves de Almeida reports that his role was to check and edit the paper.
