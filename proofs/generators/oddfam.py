#!/usr/bin/env python3
# S166 oddfam.py l [l2] [OUTDIR] : EXPLICIT (search-free) spread-k circuit codes on the ODD lines l = 3 (mod 4), l >= 15:
#     k = (l^2-l-6)/2,  n = (3k+l+1)/2,  N = 2l^2-10 = 4k+2l+2      (family 2 of S165 only reaches k = (l-1)^2/2)
# Shape: half-turn automorphism, antipodal dots, half word W0^(l-1) S with W0 = FF(.F)^((l-3)/2). (period l) and the short period
# S = W0[:l-7] + 'F.' (length l-5; F residues 0, 1, 3, .., l-8 and l-7).  Position (i,r) = l*i+r, full periods i = 0..l-2, short period
# i = l-1.  h = (l-1)/2, K = k+1 = l*h-2.  GAP FUNCTION g = K+e:
#   periods i <= h-1:      r=0: 0;  r=1: l+6;  r=3: 0;  r=5: l-7 (i <= h-2), 2l-8 (i = h-1);  odd 7 <= r <= l-6: (l+3-2r) mod l;
#                          r=l-4: l+6 (i <= h-2), 7 (i = h-1);  r=l-2: 7 (i <= h-2), 0 (i = h-1)
#   periods h+1 <= i <= l-2: r=0: 0;  r=1: l-8;  r=3: l-8;  r=5: l-8;  odd 7 <= r <= l-4: l-2-2r if r < h, 2l-2-2r if r >= h;  r=l-2: 0
#   period i = h:          as periods > h, except  r=1: 4;  odd 3 <= r <= h-4: h-1;  r=h-2: h-2
#   short period:          r=0: 0;  r=1: l-8;  r=3: 2l-6;  r=5: l-8;  odd 7 <= r <= h-2: l-2-2r;  odd h <= r <= l-8: h+1;  r=l-7: h+2
# Checked from the definition by evenfam.check (all windows + half-turn automorphism); no solver.
import sys
from evenfam import check
def build5(l):
    assert l % 4 == 3 and l >= 15
    h = (l-1)//2; k = (l*l-l-6)//2; K = k+1; n = (3*k+l+1)//2; H = l*(l-1)+l-5; N = 2*H
    assert K == l*h-2 and N == 4*k+2*l+2
    e = {}
    for i in range(l-1):
        for r in [0]+list(range(1, l-1, 2)):
            if i <= h-1:
                if r in (0, 3): x = 0
                elif r == 1: x = l+6
                elif r == 5: x = l-7 if i <= h-2 else 2*l-8
                elif r <= l-6: x = (l+3-2*r) % l
                elif r == l-4: x = l+6 if i <= h-2 else 7
                else: x = 7 if i <= h-2 else 0
            else:
                if r == 0 or r == l-2: x = 0
                elif r in (1, 3, 5): x = l-8
                else: x = l-2-2*r if r < h else 2*l-2-2*r
                if i == h:
                    if r == 1: x = 4
                    elif 3 <= r <= h-4: x = h-1
                    elif r == h-2: x = h-2
            e[l*i+r] = x
    b = l*(l-1)
    e[b] = 0; e[b+1] = l-8; e[b+3] = 2*l-6; e[b+5] = l-8
    for r in range(7, l-7, 2): e[b+r] = l-2-2*r if r <= h-2 else h+1
    e[b+l-7] = h+2
    g = {x: K+v for x, v in e.items()}
    T = [-1]*N; c = 0
    for t in range(N):
        if T[t] < 0:
            if (t % H) in g:
                u = t; cnt = 0
                while T[u] < 0: T[u] = c; u = (u+g[u % H]) % N; cnt += 1
                if u != t or cnt != 4: return None, f'coordinate starting at {t} = ({(t%H)//l},{(t%H)%l}) does not close after 4 steps'
            else: T[t] = T[t+H] = c
            c += 1
    if c != n: return None, f'{c} coordinates, expected {n}'
    return (n, k, N, H, K, T), None
if __name__ == '__main__':
    l1 = int(sys.argv[1]); l2 = int(sys.argv[2]) if len(sys.argv) > 2 else l1; outdir = sys.argv[3] if len(sys.argv) > 3 else None
    for l in range(l1, l2+1, 4):
        res, err = build5(l)
        if err: print(f'l={l}: BUILD FAILS: {err}', flush=True); continue
        n, k, N, H, K, T = res
        bad = check(n, k, N, H, T)
        print(f'l={l} (n,k,N)=({n},{k},{N}): ' + ('VALID' if bad is None else 'INVALID '+bad), flush=True)
        if bad is None and outdir:
            v = 0; out = []
            for c in T: out.append('%x' % v); v ^= 1 << c
            open(f'{outdir}/ofam_{n}_{k}_{N}.txt', 'w').write(f'# n {n} k {k} N {N} coil from the EXPLICIT odd-line family l={l} (theory/struct/even/oddfam.py, S166); transition word: '+' '.join(map(str, T))+'\n'+'\n'.join(out)+'\n')
