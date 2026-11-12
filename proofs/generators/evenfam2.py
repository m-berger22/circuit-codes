#!/usr/bin/env python3
# S166 evenfam2.py l [l2] [OUTDIR] : EXPLICIT (search-free) spread-k circuit codes on the EVEN lines l = 2 (mod 4), l >= 10:
#     k = (l^2-l-8)/2,  n = (3k+l+1)/2,  N = 2l^2-14 = 4k+2l+2   (theorem bound on these lines: k <= (l^2-l-4)/2)
# Shape: half-turn automorphism, antipodal dots, type word (P^l P')^2, P = (.F)^(l/2-1) F (length p = l-1), P' = (.F)^(l/2-4) F (length p-6).
# Position (i,r) = p*i+r (periods i = 0..l-1, short period i = l), K = k+1 = p*l/2 - 3, h = l/2, q = (l-10)/4.
# GAP FUNCTION g = K+e:
#   periods i < h:      r=1: 1;  r=3: 2q+3;  r=5: 2p-4 (i <= h-2), p-1 (i = h-1);  7 <= r <= 2q+5: p-1;  2q+7 <= r <= p-4: 1;
#                       r=p-2: 1;  r=p-1: 5 (i <= h-2), 3 (i = h-1)
#   periods h <= i < l: r=1: 2p-6;  3 <= r <= 2q+1: 1 (i >= h+1), 2q+3 (i = h);  r=2q+3: p-2q-3;  2q+5 <= r <= p-6: p-1;
#                       r=p-4, p-2: 0;  r=p-1: 3 (i <= l-2), 2p-4 (i = l-1)
#   short period:       1 <= r <= 2q+1: 1;  2q+3 <= r <= p-8: p-2q-3;  r=p-7 (last letter): 5
# Checked from the definition by evenfam.check (all windows + half-turn automorphism); no solver.
import sys
from evenfam import check
def build2(l):
    assert l % 4 == 2 and l >= 10
    p = l-1; h = l//2; q = (l-10)//4; k = (l*l-l-8)//2; K = k+1; n = (3*k+l+1)//2; H = p*l+p-6; N = 2*H
    assert K == p*h-3 and N == 4*k+2*l+2
    e = {}
    for i in range(l):
        for r in list(range(1, p-1, 2))+[p-1]:
            if i < h:
                if r == 1: x = 1
                elif r == 3: x = 2*q+3
                elif r == 5: x = 2*p-4 if i <= h-2 else p-1
                elif r <= 2*q+5: x = p-1
                elif r <= p-4: x = 1
                elif r == p-2: x = 1
                else: x = 5 if i <= h-2 else 3
            else:
                if r == 1: x = 2*p-6
                elif r <= 2*q+1: x = 1 if i >= h+1 else 2*q+3
                elif r == 2*q+3: x = p-2*q-3
                elif r <= p-6: x = p-1
                elif r in (p-4, p-2): x = 0
                else: x = 3 if i <= l-2 else 2*p-4
            e[p*i+r] = x
    for r in range(1, p-7, 2): e[p*l+r] = 1 if r <= 2*q+1 else p-2*q-3
    e[p*l+p-7] = 5
    g = {x: K+v for x, v in e.items()}
    T = [-1]*N; c = 0
    for t in range(N):
        if T[t] < 0:
            if (t % H) in g:
                u = t; cnt = 0
                while T[u] < 0: T[u] = c; u = (u+g[u % H]) % N; cnt += 1
                if u != t or cnt != 4: return None, f'coordinate starting at {t} does not close after 4 steps'
            else: T[t] = T[t+H] = c
            c += 1
    if c != n: return None, f'{c} coordinates, expected {n}'
    return (n, k, N, H, K, T), None
if __name__ == '__main__':
    l1 = int(sys.argv[1]); l2 = int(sys.argv[2]) if len(sys.argv) > 2 else l1; outdir = sys.argv[3] if len(sys.argv) > 3 else None
    for l in range(l1, l2+1, 4):
        res, err = build2(l)
        if err: print(f'l={l}: BUILD FAILS: {err}', flush=True); continue
        n, k, N, H, K, T = res
        bad = check(n, k, N, H, T)
        print(f'l={l} (n,k,N)=({n},{k},{N}): ' + ('VALID' if bad is None else 'INVALID '+bad), flush=True)
        if bad is None and outdir:
            v = 0; out = []
            for c in T: out.append('%x' % v); v ^= 1 << c
            open(f'{outdir}/efam_{n}_{k}_{N}.txt', 'w').write(f'# n {n} k {k} N {N} coil from the EXPLICIT even-line family l={l} (theory/struct/even/evenfam2.py, S166); transition word: '+' '.join(map(str, T))+'\n'+'\n'.join(out)+'\n')
