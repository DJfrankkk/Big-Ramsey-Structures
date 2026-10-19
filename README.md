# Big Ramsey structures in unrestricted languages and a finitely constrained counterexample

**Yifan Hu · Wuhan University**

[Read the manuscript](Big_Ramsey_Structures_and_Finite_Constraints_revised.pdf)

This paper studies when a countable relational structure admits a single coherent expansion recording its optimal big Ramsey colourings, and how finite forbidden configurations can obstruct this.

## Main results

1. **Big Ramsey structures in unrestricted languages.** We construct a big Ramsey structure for the generic injective relational structure in every language with finitely many symbols of each positive arity. Both the language and its arities may be unbounded. This answers the **existence part of Problem 6.3.2** of Balko et al., explicitly restated as **[Problem 8.19](https://arxiv.org/html/2501.17293v5)** by Hubička and Konečný. Here, “injective” means that relations hold only on tuples of distinct vertices; symmetry is not required.

2. **A uniform envelope theorem.** In the valuation setting considered in the paper, one embedding works simultaneously for every finite size, with envelope heights bounded by

   $$
   R(k)=2k+(k4^k+1)^2.
   $$

   The bound is independent of the language parameters and the input hypergraph. This **disproves Conjecture 4.7** of Braunfeld et al. A transfer theorem through precompact expansions turns this uniform control into compatible optimal expansion types.

3. **A finitely constrained counterexample.** We construct a finite language of maximum arity three and a finite family of irreducible forbidden structures on three or four vertices whose Fraïssé limit has **infinite singleton big Ramsey degree**. Consequently, it admits no big Ramsey structure. This gives a **negative instance of Problem 6.3.3**, even within free amalgamation classes.

   It also gives a **negative answer to the finite-language, finitely-forbidden strong-amalgamation subquestion of [Problem 6.1 in Dobrinen's ICM 2022 report](https://arxiv.org/pdf/2110.00655#page=18)**, and to the universal finiteness question in **[Question 8.4 of Coulson–Dobrinen–Patel, arXiv:2010.02034v2](https://arxiv.org/pdf/2010.02034v2#page=68)**.

The exact-degree description is an implicit minimum over self-embeddings; finding an effective enumeration remains open. The counterexample uses several relation symbols, including ordered ternary relations, and leaves the corresponding single-relation, 3-uniform hypergraph questions open.

## AI-assisted research and token usage

This work began with a selection of the author's existing research materials, including notes on discrete geometry and elementary Ramsey theory, supplied as background to GPT models. Building on those materials, **Pharos** with the model identifier **`gpt-6-astra`** was used for further mathematical exploration, proof development, model-based checking, and organization of the results. 

Before attempting Problem 6.3.2, we first worked on Problem 6.3.1. At the time, we were unaware that Problem 6.3.1 had already been solved earlier this summer, apparently because GPT-6.1 Sol had failed to identify the relevant work during its literature search. After obtaining a solution, we also asked GPT-6 Pro to solve Problem 6.3.1 independently, which it accomplished in approximately one hour. Notably, GPT-6 Pro also failed to mention that the problem had already been resolved. Consequently, the token usage reported below includes the tokens spent on solving Problem 6.3.1.

**All token figures below are approximate estimates reconstructed from the available research logs.** They cover the two projects associated with this paper, with runs on **8–9 October 2026**. Accounting coverage is incomplete, and the figures are rounded. All table entries are in **millions of tokens**.

| Research track | Uncached input | Cached input | Output | Total |
|---|---:|---:|---:|---:|
| Unrestricted languages / Problem 6.3.2 | 9.7 | 136.6 | 1.6 | 147.9 |
| Finite constraints / Problem 6.3.3 | 51.5 | 826.1 | 10.8 | 888.3 |
| **Combined** | **61.2** | **962.6** | **12.4** | **1,036.2** |

**Estimated total traffic: approximately 1.04 billion tokens**, including repeated cached context reads. **Estimated uncached input plus output: approximately 73.6 million tokens.** Reasoning tokens are included in the output column.

These estimates cover project-local main agents, workers, auxiliary agents, model-based verification, and reporting, including unsuccessful research attempts. They exclude separate manuscript-editing conversations, work outside these two projects, and calls without recorded usage. Request-level usage records were deduplicated by response ID; two rollout files had no usage record. The Problem 6.3.3 figure covers the entire research programme, including work beyond the counterexample presented here.

## Unresolved Ramsey research attempts

We also explored the following broader Ramsey questions. **As of 18 October 2026, we have not obtained a complete solution to any of these full targets.**

All figures below are **estimated millions of tokens**, reconstructed from the available logs.

| Question | Estimated total, including cached input | Estimated uncached input + output | Outcome |
|---|---:|---:|---|
| **Full Problem 6.3.3:** characterize big Ramsey degrees and big Ramsey structure existence for arbitrary finite irreducible forbidden families. | **888.3M** | **62.3M** | The counterexample in this paper and restricted results were obtained; the general classification remains unfinished. |
| **Hubička–Zucker Question 3.6 / Dobrinen's ICM Problem 6.3 (first question):** do finite big Ramsey degrees imply the existence of a big Ramsey structure for every countable Fraïssé structure? | **233.8M** | **17.0M** | No general proof or counterexample was obtained. The project was subsequently redirected. |
| **Ramsey expansion conjecture:** does every countable ultrahomogeneous structure in a finite relational language admit a finite relational expansion that remains ultrahomogeneous and has a Ramsey age? | **696.4M** | **41.9M** | Partial results under additional hypotheses were obtained; the universal conjecture was neither proved nor refuted. |

The Problem 6.3.3 row refers to the same project already included in the paper's token totals above. The two later general-conjecture attempts are additional research and are outside those totals. All figures are approximate and include exploration and model-based verification.

## Lean formalization

The proof entry point is [`Ramsey_Problems/CombinedRamsey/Revised20261018.lean`](Ramsey_Problems/CombinedRamsey/Revised20261018.lean). Its complete local import closure, together with the axiom-checking entry point, is included: **228 Lean source files** across `CombinedRamsey`, `RelationalRamsey632`, and `RamseyCommon`, plus a `RamseyCommon.lean` import index.

`RamseyCommon` contains the 16 shared tree, finite-palette, and orbit-counting modules required by the current proofs. The earlier, separate Problem 6.3.1 formalization is not included. Its main theorem was not fully formalized; the Lean verification reported here concerns the current paper's proof entry point.

The project pins **Lean 4.31.0** in `lean-toolchain` and Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in the Lake configuration. `lake-manifest.json` also pins the transitive library dependencies. Lake downloads these external libraries and their build caches.

With Lean/Elan and Git installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean Ramsey_Problems/CombinedRamsey/Revised20261018/Checks.lean
```

In VS Code, open the repository folder and then the proof entry point. The final command above runs the included transitive axiom check for the loaded project declarations.

The editable manuscript and its local journal style are in [`paper/`](paper/). The PDF is linked at the top of this README.

## References for the problems

- Balko et al., *Exact big Ramsey degrees for finitely constrained binary free amalgamation classes*, Journal of the European Mathematical Society 28 (2026), 2101–2150. [DOI](https://doi.org/10.4171/JEMS/1507).
- Braunfeld et al., *Big Ramsey degrees and infinite languages*, Advances in Combinatorics (2024), Paper No. 4. [DOI](https://doi.org/10.19086/aic.2024.4).
- Hubička and Konečný, *Twenty years of Nešetřil's classification programme of Ramsey classes*, Computer Science Review 59 (2026), 100814, **Problem 8.19**. [Postprint, arXiv:2501.17293v5](https://arxiv.org/html/2501.17293v5).
- Dobrinen, *Ramsey theory of homogeneous structures: current trends and open problems*, Proceedings of ICM 2022, Vol. 3, 1462–1486, **Problem 6.1** (finite-language, finitely-forbidden SAP subquestion) and **Problem 6.3** (listed above as unresolved). [Publisher](https://ems.press/books/standalone/275/5435), [preprint](https://arxiv.org/pdf/2110.00655).
- Coulson, Dobrinen, and Patel, *Fraïssé classes with simply characterized big Ramsey structures*, 2021 preprint, **Question 8.4 in arXiv:2010.02034v2**. [Version with the question](https://arxiv.org/pdf/2010.02034v2#page=68).
