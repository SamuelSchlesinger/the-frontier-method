#!/usr/bin/env python3
"""Validates: classical degree-potential and cubic-density specializations.

This checks arithmetic deductions, not the external graph theorems.
Sources and analytic explanations are in ../index.md.
"""

from fractions import Fraction
from math import acos, pi, sqrt


def main():
    p = 3 * acos((1 + 2 * sqrt(2)) / 4) / (2 * pi)
    print(f"baseline p={p:.10f}; A={2*p:.10f}; L={1+1/(2*p):.10f}")
    # g2=0, g3=a, 4g4=2a+1. The derivative jump must be <=0.
    for label, a in [("historical", Fraction(1, 6)), ("target", Fraction(1, 8))]:
        g4 = (2 * a + 1) / 4
        jump = (g4 - a) - a
        assert jump == Fraction(1, 4) - Fraction(3, 2) * a
        print(f"{label}: alpha={a}, g4={g4}, increment jump={jump}")
    print(f"baseline: increment jump={0.25-1.5*p:.10f} > 0")
    assert 0.25 - 1.5 * p > 0
    # The original bridge applies max{|X|, floor(N/3)+1} on N~n/2.
    print(f"original Fomin-Hoie bridge at b=p: leading max(b,1/6)={max(p,1/6):.10f}")
    print("analytic potential constraint: 4g4-2alpha>=1 and g4<=2alpha imply alpha>=1/6")
    # BCC-H Section 4.2: T(2,n)=floor((3n-3)/2), T(3,n)=2n-3.
    # For even n>=6, T2 < 3n/2 <= T3. Formula monotonicity then gives C*=3.
    for n in range(6, 10002, 2):
        m = 3 * n // 2
        assert (3 * n - 3) // 2 < m <= 2 * n - 3
    print("grooming specialization: C*(3n/2,n)=3; checked even n=6..10000")
    print("all-even-n proof: floor((3n-3)/2)=3n/2-2; 2n-3-3n/2=n/2-3>=0")
    delta = 3
    minimum_degree_bound = (delta // 2 + 1) * ((delta + 1) // 2)
    assert minimum_degree_bound == 4
    print("minimum-degree specialization at delta=3: lower bound=4")


if __name__ == "__main__":
    main()
