#!/usr/bin/env python3
"""Re-check every circuit code in codes/ from the definition.
Each file starts with '# n <n> k <k> N <N> ...' and then lists the N vertices of Q_n in hexadecimal.
Checked: N distinct vertices < 2^n, consecutive ones (cyclically) adjacent, and for all pairs
d_H(v_i, v_j) < k  =>  d_C(i, j) = d_H(v_i, v_j).   Prints l = 2n-3k-1, Byrnes' value 4k+2l and the excess N-(4k+2l).
usage: python3 check.py [files...]"""
import glob, os, re, sys
def check(fn):
    m = re.match(r'# n (\d+) k (\d+) N (\d+)', open(fn).readline()); n, k, N = map(int, m.groups())
    v = [int(x, 16) for line in open(fn) if not line.startswith('#') for x in line.split()]
    if len(v) != N or len(set(v)) != N or max(v) >= 1 << n: return None
    for i in range(N):
        vi = v[i]
        if (vi ^ v[(i + 1) % N]).bit_count() != 1: return None
        for j in range(i + 1, N):
            dh = (vi ^ v[j]).bit_count()
            if dh < k and min(j - i, N - j + i) != dh: return None
    return n, k, N
files = sys.argv[1:] or sorted(glob.glob(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'codes', '*.txt')))
bad = 0
for fn in files:
    r = check(fn)
    if r is None: bad += 1; print('INVALID', fn); continue
    n, k, N = r; l = 2 * n - 3 * k - 1
    print(f'ok  {os.path.basename(fn):28s} n={n} k={k} N={N}  l={l}  4k+2l={4*k+2*l}  excess={N-4*k-2*l}', flush=True)
print(f'{len(files)} files, {bad} invalid')
sys.exit(1 if bad else 0)
