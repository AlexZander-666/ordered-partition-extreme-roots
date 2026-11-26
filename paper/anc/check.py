"""Exact fixed-threshold checks for the reciprocal edge of ordered partition rows."""
import json
from fractions import Fraction as F
from math import comb, factorial


def raw_rows(limit, j):
    rows = [[1]]
    for n in range(1, limit + 1):
        target = [0] * (n // j + 1)
        for b in range(1, n + 1):
            shift = int(b >= j)
            choices = comb(n, b)
            for k, count in enumerate(rows[n - b]):
                target[k + shift] += choices * count
        rows.append(target)
    return rows


def mul(p, q, m):
    return [sum(p[i] * q[k-i] for i in range(k+1)) for k in range(m+1)]


def egf_coefficient(j, d, r, h):
    """[z^m] V (UV)^(d-h), via the small-block geometric series."""
    m = r + j*h
    v = [F(1)]
    for k in range(1, m+1):
        v.append(sum(v[k-i]/factorial(i) for i in range(1, min(k,j-1)+1)))
    u = [F(factorial(j), factorial(j+i)) for i in range(m+1)]
    power = mul(u, v, m)
    product = v
    k = d-h
    while k:
        if k % 2:
            product = mul(product, power, m)
        k //= 2
        if k:
            power = mul(power, power, m)
    return product[m]


def sign(poly, x):
    v = 0
    for coeff in reversed(poly):
        v = v*x + coeff
    return (v > 0) - (v < 0)


def reciprocal_tests(rows, d, r):
    # Rational y probes around the consecutive positive zeros of cos y and sinc y.
    probes = [F(0), F(2), F(5), F(8), F(11)] if r == 0 else [F(0), F(4), F(7), F(10), F(13)]
    g = F(32,9)
    inverse = rows[2*d+r][::-1]
    signs = [sign(inverse,-y*y/(g*d*d)) for y in probes]
    return dict(d=d, residue=r, probes=[str(y) for y in probes], signs=signs)


if __name__ == '__main__':
    sample_count = 0
    for j in (2,3,4,5):
        rows = raw_rows(7*j+j-1,j)
        for d in range(1,8):
            for r in range(j):
                n = j*d+r
                for h in range(min(3,d)+1):
                    assert F(rows[n][d-h]*factorial(j)**(d-h),factorial(n)) == egf_coefficient(j,d,r,h)
                    sample_count += 1
    rows = raw_rows(257, 2)
    evidence = [reciprocal_tests(rows,d,r) for d in (32,64,128) for r in range(2)]
    for case in evidence[-2:]:
        assert case['signs'] == [1,-1,1,-1,1]
    print(json.dumps(dict(exact_coefficient_checks=sample_count, probes=evidence),indent=2))
