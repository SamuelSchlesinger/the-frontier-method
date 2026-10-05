/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Compression
public import Frontier.Layouts.Gaussian

/-!
# Layout bounds for subcubic graphs

The graph-theoretic input of the lower bound, proved:

* `layoutBound_gaussian`: `LayoutBound 3 (2p)` with `p = (3/(2π)) arccos ((1 + 2√2)/4)`, so
  `2p ≈ 0.2807`. Gaussian edge scores lay out every large cubic graph on `h` vertices with
  prefix cuts at most `(p + o(1)) h` (`Frontier.Gaussian.cubicLayoutBound_gaussian`), and
  compressing a subcubic multigraph to its cubic core turns this into a layout bound with
  coefficient `2p` (`Frontier.LayoutBound.of_cubic`).
* `layoutBound_one_third`: `LayoutBound 3 (1/3)`, since `2p ≤ 9/32 < 1/3`.

## Structure of the proof

```
Frontier.Layouts.Kernel         distance kernels on graphs of maximum degree three
Frontier.Layouts.Probability    Gaussian forms; Sheppard's crossing bound; windows and tails
Frontier.Layouts.SecondMoment   concentration of counts of local events
Frontier.Layouts.Star           angles between vectors close to a common vector
Frontier.Layouts.Median         ordering a cubic graph by median edge scores
Frontier.Layouts.Gaussian       the random layout: CubicLayoutBound p
Frontier.Layouts.Compression    from cubic graphs to subcubic multigraphs
```
-/

@[expose] public section

namespace Frontier

/-- A larger coefficient gives a weaker layout bound. -/
theorem LayoutBound.mono {d : ℕ} {A A' : ℝ} (h : LayoutBound d A) (hAA' : A ≤ A') :
    LayoutBound d A' := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hconn hloop hdeg => ?_⟩
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  refine ⟨π, fun t => (hπ t).trans ?_⟩
  have : (A + η) * G.cycleRank ≤ (A' + η) * G.cycleRank := by gcongr
  linarith

/-- **Gaussian layouts.** Connected, loopless multigraphs of maximum degree three have layouts
of width `(2p + o(1)) β₁ + o(|V|)`, where `p = (3/(2π)) arccos ((1 + 2√2)/4)`. -/
theorem layoutBound_gaussian : LayoutBound 3 (2 * Gaussian.gaussianCoefficient) :=
  LayoutBound.of_cubic Gaussian.gaussianCoefficient_pos.le Gaussian.cubicLayoutBound_gaussian

/-- **The coefficient one third.** -/
theorem layoutBound_one_third : LayoutBound 3 (1 / 3) :=
  layoutBound_gaussian.mono (by linarith [Gaussian.two_mul_gaussianCoefficient_le])

end Frontier
