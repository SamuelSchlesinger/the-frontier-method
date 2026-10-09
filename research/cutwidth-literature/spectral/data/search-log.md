# Spectral search and access log

[Back to spectral review](../index.md). Search/access date: 2026-10-09.
This records the focused search coverage and evidence depth; it does not claim
exhaustive coverage of every historical paper or every citation descendant.
No private data or credentials were used in the web searches.

## Search families

1. Exact author/title searches: Csóka–Gerencsér–Harangi–Virág Gaussian processes;
   Lyons factors of IID and bisections; Lichev–Mitsche minimum bisection cubic.
2. Adjacent spectral methods: Backhausz–Szegedy–Virág Ramanujan graphings;
   Backhausz–Virág spectral measures; nonbacktracking/polynomial filter sections
   and citations in those primary texts.
3. Nonlinear local algorithms: El Alaoui–Montanari–Sellke max-cut/minimum bisection;
   Barak–Marwaha classical and quantum limitations on high-girth graphs.
4. Limits: entropy inequalities for factors of IID; random-cubic min bisection
   versus maximum cut; interpolation, RSB bounds, 2025/2026 follow-up searches.
5. Threshold coherence: Gallo–Grigoriadis–Tarjan parametric maximum flow;
   Chambolle–Darbon discrete total variation and coarea; Plackett normal integrals.
6. Concentration/comparison: Janson partly dependent random variables;
   Slepian one-sided barriers (metadata found, not used as a load-bearing source).

Search results from secondary indexes were used only for discovery. Claims in
the documents use primary arXiv, publisher, author, or institutional records.

## Primary texts read at the load-bearing portions

| Source | Portions read | Primary access |
|---|---|---|
| CGHV | Wave construction and approximation, Theorems 3–5, Section 3 | [Author PDF](https://users.renyi.hu/~harangi/papers/ind_set.pdf), [record](https://arxiv.org/abs/1305.3977) |
| Lyons | FIID/block approximation, full Section 4 including Theorem 4.1, strict gain and transfer | [Author PDF](https://rdlyons.pages.iu.edu/pdf/fiid.pdf), [record](https://arxiv.org/abs/1401.4197) |
| Lichev–Mitsche | Version-of-record introduction, Section 6, border-cherry exchange and numerical refinement | [Journal PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i2p40/pdf/), [record](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v30i2p40) |
| Backhausz–Szegedy–Virág | Correlation bound and spectral interpretation | [Full PDF](https://arxiv.org/pdf/1305.6784), [publisher](https://doi.org/10.1002/rsa.20562) |
| Backhausz–Virág | Theorems 2/4 and Sections 6.3–6.5 | [Full PDF](https://arxiv.org/pdf/1505.07412), [institutional record](https://real.mtak.hu/74276/) |
| Backhausz–Gerencsér–Harangi | Edge–vertex theorem, general covers, stronger entropy inequalities | [Author PDF](https://www.renyi.hu/~harangi/papers/entropy_inequalities.pdf), [publisher](https://ems.press/journals/ggd/articles/15855) |
| Dembo–Montanari–Sen | Main asymptotic statements and interpolation setup | [Full PDF](https://arxiv.org/pdf/1503.03923), [record](https://arxiv.org/abs/1503.03923) |
| El Alaoui–Montanari–Sellke | Assumption 1, Theorem 1.7, algorithms and Gaussian special case, final rounding | [Full PDF](https://arxiv.org/pdf/2111.06813), [publisher](https://doi.org/10.1002/rsa.21149) |
| Barak–Marwaha | Main results, locality definitions, centred one-local obstruction | [Full PDF](https://arxiv.org/pdf/2106.05900), [proceedings](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2022.14) |
| Chambolle–Darbon | Sections 2–4, especially discrete Proposition 3.3 | [Author PDF](https://ww3.math.ucla.edu/camreport/cam08-19.pdf), [publisher](https://doi.org/10.1007/s11263-009-0238-9) |
| Zdeborová–Boettcher | Conjecture and random-regular scope | [Full PDF](https://arxiv.org/pdf/0912.4861), [laboratory record](https://laro.lanl.gov/esploro/outputs/journalArticle/A-conjecture-on-the-maximum-cut/9916364087203761) |
| Coja-Oghlan et al. | Introduction and Section 3.2 on interpolation/max-cut | [Accepted PDF](https://eprints.lse.ac.uk/113471/1/Ising_antiferromagnet_revised_clean.pdf), [publisher](https://doi.org/10.1137/20M137999X) |
| Harangi | Main 2-RSB theorem, normalization and Table 1 | [Full HTML v1](https://arxiv.org/html/2506.21296v1), [record](https://arxiv.org/abs/2506.21296) |
| Aronow–Lopatto | Theorem 1.1, interpolation overview, conclusion and references | [Full HTML v1](https://arxiv.org/html/2609.19057v1), [record](https://arxiv.org/abs/2609.19057) |

## Limited access and audit decisions

- Gallo–Grigoriadis–Tarjan: publisher abstract/metadata and indexed Princeton
  report abstract accessed; full report fetch failed. The detailed patch proof
  is provided independently and does not depend on an unread runtime theorem.
- Janson: publisher abstract and indexed author introduction accessed. Both web
  full-PDF and local `curl` attempts failed; the latter could not resolve the
  host under the network sandbox. No escalation was needed to finish the review.
- Plackett: title, author, pages and DOI verified through publisher/archive
  metadata, full text not obtained. The special differentiation argument used
  for the threshold profile is written out in [patches.md](../patches.md).
- Slepian 1962: publisher metadata/abstract verified; not included in the
  bibliography because no detailed theorem from it is needed.
- Publisher full text for El Alaoui–Montanari–Sellke failed. The conditional
  assumption is verified in the accessed full arXiv paper and reported as such.
- Harangi's numerical table was read, not independently interval-certified.
  A numeric parameter choice in a rigorous variational inequality is different
  from solving the global optimization problem exactly.
- The Aronow–Lopatto arXiv record and full HTML agree on title, authors and
  theorem, but show July dates with an identifier beginning `2609`. Only the
  version identifier and year are cited, with this metadata discrepancy disclosed.

## Freshness and omitted leads

The 2025 Harangi preprint and 2026 Aronow–Lopatto preprint were found during
the live search. Their inequality direction and parameter are explicitly
distinguished from the desired universal minimum-layout upper bound.
The inspected RSB records do not settle the minimum-bisection complement
conjecture. No inference is made from the maximum-bisection result to it.

A current search also found *Factorization norms and an inverse theorem for
MaxCut* (Balla, Hambardzumyan, Tomon, publisher DOI 10.1007/s00208-026-03355-2).
Only the primary abstract/metadata were seen; it was not treated as an
application theorem for sparse cubic minimum cutwidth. This is a follow-up
lead, not an omitted proof ingredient or a claim that the full paper was read.

## Local deductions and validation

The proposal note proves nested patch minimization, derives the Gaussian
threshold profile, and identifies the exact double-minority charging defect.
The script [check_proposals.py](check_proposals.py) uses the standard library
and writes [check_proposals-output.json](check_proposals-output.json).
It contains no Monte Carlo sampling. Finite enumeration and floating-point
arithmetic check the stated examples; they do not certify an asymptotic gain.
