# Parameter search and source-access log

[Parameter review](../index.md) · [Finite validation](validate_conversions.py)

Search date: 2026-10-09. This records the targeted search performed; it does not
claim complete coverage of all historical publications. Results were used as leads,
then checked against publisher, author-hosted, or arXiv primary material.

| Search family and representative query | Checked source path | Result for this review |
|---|---|---|
| `cutwidth pathwidth maximum degree three Korach Solel Kinnersley` | Kinnersley publisher abstract; Golovach original publisher abstract; Fomin author PDF | Exact additive-two subcubic conversion identified |
| `Golovach cut width vertex separation number line graph 1993` | MathNet original publication record, cross-checked with Harvey–Wood Section 2 | Line graph, connectedness, and one-edge exception retained |
| `linear width pathwidth subcubic graphs cutwidth plus one` | Fomin Sections 4–5 | Minimum-degree condition for linear-width retained; false original-graph equality rejected |
| `Harvey Wood treewidth line graphs congestion cutwidth` | Author PDF, Theorems 2.4 and 2.6; Monash publication record | Exact node-congestion objective identified |
| `Seymour Thomas call routing ratcatcher Combinatorica 1994 carving width` | Seymour author PDF, Sections 6–7 | Carving/branch distinction and planarity restriction retained |
| `Oum Seymour approximating clique-width branch-width symmetric submodular 2006 pdf` | Author PDF; publication metadata at author's institution | Oracle connectivity framework; search also discovered 2026 advance |
| `Branch-width of connectivity functions is fixed-parameter tractable` | arXiv:2601.04756v2, Theorem 1.1 | Exact 2026 oracle algorithm checked; no extremal bound inferred |
| `Kashyap matroid pathwidth code trellis complexity Forney branch complexity` | Author PDFs and arXiv versions of 2008/2009 papers | State/constraint distinction and fixed-tree minimality checked |
| `Forney Codes on graphs normal realizations 2001 pdf` | Original DOI inaccessible; author's 2018 paper, reference [5] and Section II | Historical source credited; substantive use supported by accessible later primary paper |
| `Treewidth of MDS and Reed-Muller Codes 2012 DOI` | Full preprint, Theorem 5; author's publication page and IEEE DOI link | Equality barrier and constraint-based convention checked |
| `Jeong Kim Oum constructive algorithm path-width matroids 2016 2018` | Final 2017 arXiv version and journal reference | Fixed-field constructive algorithm; no quantitative supply consequence |
| `Boolean-width of graphs Bui-Xuan Telle Vatshelle 2011 doi pdf` | Author preprint Section 2 and publisher metadata | Neighbourhood-union equivalence recorded |
| `New Width Parameters of Graphs Vatshelle thesis pdf` | University record; repository redirected to a dynamic page | Historical thesis located but not treated as read |
| `On the Hardness of Generalized Domination Problems Parameterized by Mim-Width` | Dagstuhl full text Section 2 | Precise modern mim-width definition checked |
| `Amarilli Capelli Monet Senellart connecting width knowledge compilation 2020 pathwidth complete uOBDD` | Author full text Theorem 4.4 and Section 7 | Explicit doubled exponent retained |
| `Connecting Knowledge Compilation Classes and Width Parameters 64 2020` | Author final publication record; title-correction record | Early PDF title issue identified; corrected title used |
| Existing repository citation to Bova et al. | Official IJCAI 2016 proceedings full text | Certificate rectangle/splicing antecedent checked |

## Access failures and exclusions

- The original Forney 2001 DOI and one CiteSeerX PDF failed to provide full text.
- Golovach's primary abstract was available in search extraction; a subsequent open
  returned an error. The full Russian paper was not read. Its inequality was checked
  in two accessible research papers, Fomin 2003 and Harvey–Wood 2018.
- The old Bergen author PDF for Belmonte–Vatshelle redirected to a department page.
  An arXiv predecessor was inspected, but no claim relies on the inaccessible file.
- Vatshelle's thesis repository redirected to a dynamically rendered metadata page;
  the thesis was not counted among the 18 cited, checked references.
- The Thilikos 2000 linear-width paper was located through its publisher abstract;
  no inaccessible theorem was assumed. The needed inequalities came from Fomin.
- Secondary summaries appeared in search results but were not used as theorem
  evidence. In particular the claimed equality with original-graph pathwidth plus
  one conflicts with the verified `K3,3` computation.

## Validation boundary

The Python checker uses exact subset dynamic programming for graph widths and
explicit binary quotient classes for code profiles. Its independent expected values
are in [validation-output.txt](validation-output.txt). It also verifies a general
tripartition identity on all 729 partitions of one multigraph and a four-vertex
common-order counterexample. These finite checks do not establish a universal
asymptotic improvement. Bibliographic details and per-source access depth are in the
[master bibliography](../../sources.md).
