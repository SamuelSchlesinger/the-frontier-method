#!/usr/bin/env python3
"""Bounded CPU/CUDA screening benchmark, NOT a patch-gain certificate.

Sample one limiting cubic-tree Gaussian law, then evaluate the exact two-vertex
patch gain at five thresholds. This does not cover arbitrary cubic graphs,
threshold intervals, covariance uncertainty, or integration error.

Requires NumPy; --backend cuda additionally requires a CUDA-enabled PyTorch.
Example: python3 benchmark_patch_gain.py --backend cuda --dtype float32
"""

import argparse
from collections import deque
import json
import math
import os
import platform
import statistics
import time

import numpy as np


EDGES = [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5),
         (2, 6), (2, 7), (3, 8), (3, 9),
         (4, 10), (4, 11), (5, 12), (5, 13)]
THRESHOLDS = (-0.15, -0.075, 0.0, 0.075, 0.15)
WEIGHTS = (1 << np.arange(13)).astype(np.int64)


def model():
    adjacency = [[] for _ in range(14)]
    for u, v in EDGES:
        adjacency[u].append(v)
        adjacency[v].append(u)
    distance = np.zeros((14, 14), dtype=int)
    for root in range(14):
        seen, queue = {root}, deque([root])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if v not in seen:
                    seen.add(v)
                    distance[root, v] = distance[root, u] + 1
                    queue.append(v)
    vertex_cov = (1 + distance / 3) * np.exp2(-distance / 2)
    incidence = np.zeros((13, 14))
    for j, (u, v) in enumerate(EDGES):
        incidence[j, u] = incidence[j, v] = 1 / math.sqrt(2 + 4 * math.sqrt(2) / 3)
    covariance = incidence @ vertex_cov @ incidence.T
    values, vectors = np.linalg.eigh(covariance)
    if values.min() < -1e-10 or not np.allclose(np.diag(covariance), 1, atol=1e-12, rtol=0):
        raise RuntimeError("Invalid floating-point tree covariance")
    # Zero tiny numerical negative eigenvalues; this is not interval arithmetic.
    factor = vectors * np.sqrt(np.maximum(values, 0))

    patterns = ((np.arange(8192)[:, None] >> np.arange(13)) & 1).astype(bool)
    node_edges = [[j for j, edge in enumerate(EDGES) if v in edge] for v in range(6)]
    colors = np.column_stack([patterns[:, js].sum(axis=1) >= 2 for js in node_edges])
    old = sum((colors[:, u] != colors[:, v]).astype(int) for u, v in EDGES[:5])
    best = np.full(8192, 6, dtype=int)
    for state in range(4):
        new = colors.copy()
        new[:, 0], new[:, 1] = bool(state & 1), bool(state & 2)
        cut = sum((new[:, u] != new[:, v]).astype(int) for u, v in EDGES[:5])
        best = np.minimum(best, cut)
    gain = (old - best).astype(np.int64)

    # Independently count the four possible patch assignments by boundary sums.
    a = colors[:, 2:4].sum(axis=1)
    b = colors[:, 4:6].sum(axis=1)
    direct_minimum = np.minimum.reduce([a + b, 4 - a - b, 3 - a + b, 3 + a - b])
    if not np.array_equal(best, direct_minimum) or gain.min() < 0 or gain.max() > 5:
        raise RuntimeError("Exact gain table failed its independent check")
    if not np.array_equal(gain, gain[::-1]):
        raise RuntimeError("Gain table violates color-complement symmetry")
    return factor, gain, {"minimum_eigenvalue_before_clipping": float(values.min()),
                          "factorization_max_error": float(np.max(np.abs(factor @ factor.T - covariance))),
                          "exact_lookup_patterns_checked": 8192}


def numpy_gains(scores, table):
    return np.column_stack([table[(scores < t) @ WEIGHTS] for t in THRESHOLDS])


def positive_int(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=("numpy", "cuda"), default="numpy")
    parser.add_argument("--dtype", choices=("float64", "float32"), default="float64")
    parser.add_argument("--samples", type=positive_int, default=1_000_000)
    parser.add_argument("--batch", type=positive_int, default=100_000)
    parser.add_argument("--repeats", type=positive_int, default=3)
    parser.add_argument("--seed", type=int, default=71943)
    args = parser.parse_args()
    setup_start = time.perf_counter()
    factor64, table, checks = model()
    dtype = np.dtype(args.dtype)
    factor = factor64.astype(dtype)
    metadata = {"python": platform.python_version(), "numpy": np.__version__,
                "platform": platform.platform(),
                "thread_environment": {k: os.environ.get(k) for k in
                    ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "VECLIB_MAXIMUM_THREADS")}}
    torch = None
    if args.backend == "cuda":
        try:
            import torch
        except ImportError:
            parser.error("CUDA backend requires an existing CUDA-enabled PyTorch installation")
        if not torch.cuda.is_available():
            parser.error("PyTorch cannot access CUDA; no CPU fallback was run")
        torch.set_float32_matmul_precision("highest")
        torch.manual_seed(args.seed)
        gpu_factor = torch.as_tensor(factor.T.copy(), device="cuda")
        gpu_table = torch.as_tensor(table, device="cuda")
        gpu_weights = torch.as_tensor(WEIGHTS, device="cuda")

        def cuda_gains(scores):
            return torch.stack([gpu_table[((scores < t).to(torch.int64) * gpu_weights).sum(dim=1)]
                                for t in THRESHOLDS], dim=1)

        # Device integer lookup must agree exactly for identical supplied scores.
        probe = np.random.default_rng(1001).standard_normal((4096, 13)).astype(dtype)
        wanted = numpy_gains(probe, table)
        actual = cuda_gains(torch.as_tensor(probe, device="cuda")).cpu().numpy()
        if not np.array_equal(wanted, actual):
            raise RuntimeError("CUDA gain lookup disagrees with NumPy")
        # Compare factor application in the selected precision, separately from RNG.
        scores_cpu = probe @ factor.T
        scores_gpu = (torch.as_tensor(probe, device="cuda") @ gpu_factor).cpu().numpy()
        tolerance = 2e-5 if args.dtype == "float32" else 1e-11
        if not np.allclose(scores_cpu, scores_gpu, atol=tolerance, rtol=tolerance):
            raise RuntimeError("CUDA factor application disagrees with NumPy")
        checks.update({"cuda_lookup_probe_samples": len(probe),
                       "cuda_factor_max_difference": float(np.max(np.abs(scores_cpu - scores_gpu))),
                       "cuda_factor_threshold_gain_mismatches": int(np.count_nonzero(
                           numpy_gains(scores_cpu, table) != numpy_gains(scores_gpu, table)))})
        metadata.update({"torch": torch.__version__, "cuda_runtime": torch.version.cuda,
                         "gpu": torch.cuda.get_device_name(),
                         "gpu_total_memory_bytes": torch.cuda.get_device_properties(0).total_memory,
                         "float32_matmul_precision": torch.get_float32_matmul_precision()})
        torch.cuda.synchronize()

    rng = np.random.default_rng(args.seed)

    def trial(samples):
        if torch is not None:
            torch.cuda.synchronize()
        started = time.perf_counter()
        totals = np.zeros(5, dtype=np.int64) if torch is None else torch.zeros(5, dtype=torch.int64, device="cuda")
        for start in range(0, samples, args.batch):
            count = min(args.batch, samples - start)
            if torch is None:
                scores = rng.standard_normal((count, 13), dtype=dtype.type) @ factor.T
                totals += numpy_gains(scores, table).sum(axis=0)
            else:
                scores = torch.randn((count, 13), dtype=gpu_factor.dtype, device="cuda") @ gpu_factor
                totals += cuda_gains(scores).sum(dim=0)
        if torch is not None:
            # Include completed GPU work and result transfer, not just enqueue time.
            totals = totals.cpu().numpy()
            torch.cuda.synchronize()
        elapsed = time.perf_counter() - started
        return {"wall_seconds": elapsed, "gain_sums": totals.tolist(),
                "sample_mean_gains_per_patch": (totals / samples).tolist()}

    setup_seconds = time.perf_counter() - setup_start
    trial(min(args.samples, args.batch))
    if torch is not None:
        torch.cuda.reset_peak_memory_stats()
    runs = [trial(args.samples) for _ in range(args.repeats)]
    median = statistics.median(run["wall_seconds"] for run in runs)
    result = {"purpose": "screening throughput only; not certified numerical integration",
              "model": "one limiting cubic-tree two-vertex patch; 13 Gaussian coordinates",
              "configuration": vars(args), "thresholds": THRESHOLDS,
              "environment": metadata, "validation": checks,
              "setup_and_validation_seconds": setup_seconds, "runs": runs,
              "median_wall_seconds": median, "samples_per_second": args.samples / median,
              "same_workload_10000_evaluations_hours": 10000 * median / 3600}
    if torch is not None:
        result["cuda_peak_allocated_bytes"] = torch.cuda.max_memory_allocated()
        result["cuda_peak_reserved_bytes"] = torch.cuda.max_memory_reserved()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
