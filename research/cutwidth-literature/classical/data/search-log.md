# Classical literature search log

Back to the [classical review](../index.md). Searches and access checks conducted
2026-10-09. This records the search route and its limitations; it is not a claim
that all indexed results or all citations of the recovered papers were read.

## Search questions and exact query families

| Query or family | What it resolved |
| --- | --- |
| `"cutwidth" "cubic" upper bound 2025`; `"cutwidth" "cubic" "2026"`; `"pathwidth" "cubic" "improved" bound` | Screened for a newer universal coefficient; no stronger relevant theorem was verified. Found the 2025 cubic-treewidth hardness paper and restricted-family 2026 results. |
| `"Fomin" "Høie" "Pathwidth" pdf`; `"Pathwidth of cubic graphs and exact algorithms" filetype:pdf`; `Fedor Fomin publications Høie 2006 pdf pathwidth` | Recovered the full published 2006 paper on the author's current GitHub site after old Bergen/CiteSeer links failed. Read Lemma 4 and Theorem 5 and extracted the anchored-completion bottleneck. |
| `"Monien" "Preis" "Upper bounds on the bisection width" pdf`; `"Upper bounds on the bisection width" "ps"` | Verified 2006 publication metadata and publisher-rendered Theorem 1, Section 1.3 local-improvement method, and simple-graph convention. |
| `"Korach" "Solel" "Tree-width, path-width" pdf` | Verified publisher abstract and degree/treewidth/logarithm conversion; full original proof remained unavailable. |
| `"Diaz" "Petit" "Serna" "survey of graph layout" pdf`; `"A survey of graph layout problems" pdf`; `"Addenda to the Survey of Layout Problems" "2011" "105"` | Verified 2002 survey metadata, read the 2011 update, and recovered Petit's 2001 thesis as a search aid. The thesis was not substituted for the 2002 publication. |
| `"pathwidth" "cubic" "improved" bound`; `"A general reduction theorem" "pathwidth"` | Found Edwards–McDermid 2015; read Sections 3 and 5 of the accepted manuscript and checked the parameter interval before attempting any substitution. |
| `"cutwidth" "search number" "Corollary 3.3"`; `"The vertex separation and search number of a graph" pdf`; `"On minimizing width in linear layouts" pdf` | Traced the subcubic `cw<=pw+2` chain to primary publisher abstracts and to its explicit use in the full 2025 proof. |
| `"The vertex separation number of a graph equals its path-width" site:sciencedirect.com` | Verified Kinnersley 1992's exact equivalence and bibliographic record. |
| `"On the cutwidth and the topological bandwidth of a tree" pdf`; `"Graphs with small bandwidth and cutwidth" pdf` | Screened the tree-layout/topological-bandwidth branch; primary theorem text for Chung 1985 and publisher abstract for Chung–Seymour 1989. |
| `"cutwidth" "Bermond" 2025`; `"New lower bounds on the cutwidth of graphs" pdf`; `"cutwidth" "Bermond" "hal"` | Found the 2025 publication and recovered full HAL manuscript. Checked that the new bounds are lower bounds; specialized the grooming formula to cubic edge density. |
| `"cutwidth" "Gaar" "Puges" "Wiegele"` | Recovered published metadata and full arXiv v4. Checked SDP objective, rounded orders, and sparse-instance limitations. |
| `"Bansal" "cutwidth" "log" approximation`; `"cutwidth" "approximation" "2025"` | Recovered FOCS 2024 full preprint and ITCS 2025 full publisher text; separated approximation ratios from absolute universal bounds. |
| `"cutwidth" "algorithms" "Giannopoulou" "Pilipczuk"`; `"Cutwidth I" "linear time" pdf`; `"Cutwidth II" site:sciencedirect.com` | Verified fixed-width algorithm roles and immersion-obstruction size; checked original abstracts and full 2017 preprint. |
| `"A note on exact algorithms for vertex ordering problems on graphs" pdf`; same title restricted to `fedorvf.github.io` | Read published Theorems 1, 3, 10 and subset recurrence; retained as the first small-core experimental baseline. |

## Recovered sources and access caveats

- Fomin–Høie: the old `www.ii.uib.no/publikasjoner/texrap/pdf/2005-298.pdf`
  URL redirected to a department page. CiteSeer download returned 404.
  Successful primary copy: <https://fedorvf.github.io/articles/2006/2006b.pdf>.
- Monien–Preis: DOI resolved through a publisher endpoint that sometimes failed
  direct opening, but indexed publisher full-text rendering exposed Theorem 1
  and relevant Sections 1–3. The Paderborn institutional record says that it
  has no uploaded full text. No claim to independently checking the full proof.
- Edwards–McDermid: web PDF extraction succeeded at
  <https://discovery.dundee.ac.uk/ws/files/6880233/edwmcd_2_.pdf>;
  a separate direct download returned 403. The extracted manuscript contains
  the full Sections 3 and 5 used in the review.
- Bermond et al.: `hal-04774458` is the older 2024 preprint. The reviewed
  2025 manuscript is <https://hal.science/hal-05083322v1>, retrieved via
  <https://hal.science/hal-05083322/document>. The web renderer met a HAL
  challenge; direct PDF retrieval succeeded. The PDF front matter identifies
  the four authors, journal DOI, and 2025-05-24 deposit.
- Gaar et al.: journal publication is 2024, while arXiv began in 2023;
  the reviewed version is <https://arxiv.org/abs/2301.03900v4> dated 2024-12-04.
  Journal metadata was checked separately. Ancillary solver code was not run.
- Petit's 2011 PDF was downloaded from the EATCS publisher and converted to text.
  The 2002 ACM survey PDF returned 403. Bibliographic metadata and abstract were
  verified without treating that as full-text access.
- Makedon–Sudborough 1989, Ellis–Sudborough–Turner 1994, Kinnersley 1992,
  Korach–Solel 1993, and Chung–Seymour 1989: original publisher abstracts only.
  The 2025 cubic-treewidth paper gives an explicit, fully read modern use of
  the search-number conversion, but does not replace reading the old proofs.

## Coverage boundaries and handoff

The review follows historical surveys forward to the principal cubic supply
theorems and to relevant 2024–2025 optimization papers. It does not enumerate
every special graph family, every metaheuristic, every weighted/directed
variant, or every publication citing the historical survey. Searches with
2026 terms found restricted-family and adjacent-parameter work; no unverified
2026 result is presented as a new universal cutwidth theorem.

Spectral expansion, random-regular bisections, factor-of-IID constructions,
large-girth transfer, separator profiles, and semantic capacity are owned by
the other review branches. This branch did not use those topics as shortcuts
around the same-order and arbitrary-graph requirements.

The validation script checks arithmetic deductions only. The complete-order
dynamic program and SDP methods are recommendations for a subsequent
experiment, not implementations or experiments completed by this review.
