/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Rectangle
public import Frontier.Sweep
public import Frontier.Multigraph
public import Frontier.Network
public import Frontier.Compiler
public import Frontier.Reduction
public import Frontier.LowerBound
public import Frontier.Layouts
public import Frontier.Main

/-!
# The frontier method

A circuit lower bound from graph layouts, in five independent pieces:

* `Frontier.Rectangle`: rectangle-free sets, the only property of the hard set, and the support
  lemma.
* `Frontier.Sweep`: sweeps, an abstract read-once protocol, and the frontier counting lemma
  `Frontier.Sweep.ncard_le`. No graphs or circuits appear.
* `Frontier.Multigraph` and `Frontier.Network`: layouts, the layout hypothesis
  `Frontier.LayoutBound`, constraint networks, the separator lemma, and the sweep of a network
  along a layout.
* `Frontier.Compiler`: circuits of fan-in `r` over any basis become exact constraint networks
  of maximum degree `r + 1` and cycle rank at most `(r - 1) s + 1 - |read|`.
* `Frontier.Reduction` and `Frontier.LowerBound`: a small circuit yields a graph of small cycle
  rank all of whose layouts are wide; the layout hypothesis finishes the proof.

* `Frontier.Layouts`: the layout bound for subcubic graphs, proved with Gaussian edge scores.

The main theorem is `Frontier.lowerBound`: under `LayoutBound (r + 1) A`, circuits of fan-in at
most `r` deciding dense rectangle-free sets satisfy `(r - 1) s > (1 + 1/A - ε) n`. For fan-in
two (`Frontier.lowerBound_fanInTwo`) this is `s > (L - ε) n` with `L = 1 + 1/A`. The layout
bound holds with `A = (3/π) arccos ((1 + 2√2)/4)` (`Frontier.layoutBound_gaussian`), giving the
unconditional `Frontier.lowerBound_gaussian`, with `L ≈ 4.5625`, and `Frontier.lowerBound_four`.
-/
