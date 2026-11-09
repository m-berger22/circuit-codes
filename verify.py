#!/usr/bin/env python3
"""Independent checker for spread-k circuit codes (coils) and k-snakes in the n-cube.
usage: verify.py FILE N K [open]      (FILE: hex vertex list, '#' lines ignored, .gz ok)
       verify.py --all                (checks every entry of records.tsv)
Definition (Byrnes 2016): cycle v_0..v_{L-1} in Q_n is a circuit code of spread k iff for all i != j
    d_H(v_i,v_j) < k  implies  d_C(i,j) = d_H(v_i,v_j)        (d_C = distance along the cycle)
which is equivalent to: d_C < k => d_H = d_C, and d_C >= k => d_H >= k.  For a snake ('open'), d_C is the path
distance and the length is the number of edges.  Requires numpy."""
import sys, gzip, itertools, numpy as np

def load(fn):
    op = gzip.open if fn.endswith('.gz') else open
    with op(fn, 'rt') as f:
        return np.array([int(t, 16) for l in f if not l.startswith('#') for t in l.split()], dtype=np.int64)

def pc(x): return np.bitwise_count(x)

def check(v, n, k, closed=True):
    L = len(v)
    if L < 2 * k and closed: return 'too short'
    if v.min() < 0 or v.max() >= 1 << n: return 'vertex out of range'
    if len(np.unique(v)) != L: return 'repeated vertex'
    idx = np.arange(L)
    # near pairs along the code: offsets 1..k-1 must have Hamming distance = offset
    for d in range(1, k):
        if closed: w = v ^ np.roll(v, -d)
        else: w = v[:-d] ^ v[d:]
        if np.any(pc(w) != d): return f'pair at code distance {d} has wrong Hamming distance'
    def cdist(i, j):
        d = np.abs(i - j)
        return np.minimum(d, L - d) if closed else d
    ball = sum(len(list(itertools.combinations(range(n), w))) for w in range(1, k))
    if L * ball < L * L // 2:   # enumerate Hamming balls of radius k-1 around every vertex
        order = np.argsort(v); sv = v[order]
        for w in range(1, k):
            for bits in itertools.combinations(range(n), w):
                m = sum(1 << b for b in bits)
                t = v ^ m
                p = np.searchsorted(sv, t); p[p == L] = 0
                hit = sv[p] == t
                if np.any(cdist(idx[hit], order[p[hit]]) != w): return f'two vertices at Hamming distance {w} are not {w} apart on the code'
    else:                        # all pairs, row by row
        for i in range(L - 1):
            j = idx[i + 1:]
            dh = pc(v[i] ^ v[i + 1:]); dc = cdist(i, j)
            if np.any((dh < k) & (dc != dh)): return f'violation at vertex {i}'
    return None

def main(a):
    if a and a[0] == '--all':
        import csv, os
        base = os.path.dirname(os.path.abspath(__file__)); bad = 0
        for r in csv.DictReader(open(os.path.join(base, 'records.tsv')), delimiter='\t'):
            v = load(os.path.join(base, r['file'])); n, k = int(r['n']), int(r['k'])
            closed = r['kind'] == 'coil'; length = len(v) if closed else len(v) - 1
            err = check(v, n, k, closed)
            if length != int(r['new_lower_bound']): err = f'length {length} != table'
            print(f"{r['kind']} n={n} k={k} length={length}: {'VALID' if err is None else 'INVALID: ' + err}", flush=True)
            bad += err is not None
        print('ALL VALID' if bad == 0 else f'{bad} INVALID'); return bad
    fn, n, k = a[0], int(a[1]), int(a[2]); closed = not (len(a) > 3 and a[3] == 'open')
    v = load(fn); err = check(v, n, k, closed)
    print(f"{fn}: {'coil' if closed else 'snake'} n={n} k={k} length={len(v) if closed else len(v)-1}: {'VALID' if err is None else 'INVALID: ' + err}")
    return err is not None

if __name__ == '__main__': sys.exit(1 if main(sys.argv[1:]) else 0)
