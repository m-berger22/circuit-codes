#!/usr/bin/env python3
# S166 evenfam.py l [l2] [OUTDIR] : EXPLICIT (search-free) spread-k circuit codes on the EVEN lines l = 0 (mod 4), l >= 8:
#     k = (l^2-l-6)/2,  n = (3k+l+1)/2,  N = 2l^2-10 = 4k+2l+2   (2 more than Byrnes' 4k+2l; the theorem bound is k <= (l^2-l-2)/2)
# Shape: half-turn automorphism t -> t+H (H = N/2), antipodal dots, type word (P^l P')^2 with P = (.F)^(l/2-1) F (length p = l-1)
# and P' = (.F)^(l/2-3) F (length p-4).  Position (i,r) = p*i+r (period i = 0..l-1; the short period is i = l).  K = k+1 = p*l/2 - 2.
# GAP FUNCTION g (distance to the next occurrence of the same coordinate), e = g-K, h = l/2:
#   periods i < h:        r=1: 0;  r=3: 2p-3 (i <= h-2), p (i = h-1);  5 <= r <= p-4 odd: 0 if r = 1 mod 4, p if r = 3 mod 4;
#                         r=p-2: 0;  r=p-1: 4 (i <= h-2), 2 (i = h-1)
#   periods h <= i < l:   r=1: 2p-5;  3 <= r <= p-6 odd: p if r = 3 mod 4, 0 if r = 1 mod 4;  r=p-4: 1;  r=p-2: 1;
#                         r=p-1: 2 (i <= l-2), 2p-3 (i = l-1)
#   short period (i = l): 1 <= r <= p-6 odd: 0 if r = 1 mod 4, p if r = 3 mod 4;  r=p-5 (last letter): 4
# The code is checked from the definition (all windows, via the half-turn automorphism which is checked too), no solver.
import sys, os
def build(l):
    assert l % 4 == 0 and l >= 8
    p = l-1; h = l//2; k = (l*l-l-6)//2; K = k+1; n = (3*k+l+1)//2; H = p*l+p-4; N = 2*H
    assert K == p*h-2 and N == 4*k+2*l+2
    e = {}
    for i in range(l):
        for r in list(range(1, p-1, 2))+[p-1]:
            if i < h:
                if r == 1: x = 0
                elif r == 3: x = 2*p-3 if i <= h-2 else p
                elif r <= p-4: x = 0 if r % 4 == 1 else p
                elif r == p-2: x = 0
                else: x = 4 if i <= h-2 else 2
            else:
                if r == 1: x = 2*p-5
                elif r <= p-6: x = p if r % 4 == 3 else 0
                elif r in (p-4, p-2): x = 1
                else: x = 2 if i <= l-2 else 2*p-3
            e[p*i+r] = x
    for r in range(1, p-5, 2): e[p*l+r] = 0 if r % 4 == 1 else p
    e[p*l+p-5] = 4
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
def check(n, k, N, H, T):
    """spread-k coil from the definition: for every window [t,t+L), 1 <= L <= N/2: odd(W) = L if L < k, >= k otherwise
    (t < H suffices after checking that t -> t+H is an automorphism; arcs longer than N/2 have the same odd count as their complement)"""
    mp = {}
    for t in range(N):
        if mp.setdefault(T[t], T[(t+H) % N]) != T[(t+H) % N]: return 'no half-turn automorphism'
    if len(set(mp.values())) != n: return 'automorphism not a bijection'
    cntall = [0]*n
    for c in T: cntall[c] += 1
    if any(v % 2 for v in cntall): return 'word does not close'
    par = [0]*n
    for t in range(H):
        odd = 0
        for L in range(1, H+1):
            c = T[(t+L-1) % N]
            if par[c]: odd -= 1
            else: odd += 1
            par[c] ^= 1
            if (L < k and odd != L) or (L >= k and odd < k):
                return f'window t={t} L={L}: odd={odd}'
        for L in range(1, H+1): par[T[(t+L-1) % N]] = 0
    return None
if __name__ == '__main__':
    l1 = int(sys.argv[1]); l2 = int(sys.argv[2]) if len(sys.argv) > 2 else l1; outdir = sys.argv[3] if len(sys.argv) > 3 else None
    for l in range(l1, l2+1, 4):
        res, err = build(l)
        if err: print(f'l={l}: BUILD FAILS: {err}', flush=True); continue
        n, k, N, H, K, T = res
        bad = check(n, k, N, H, T)
        print(f'l={l} (n,k,N)=({n},{k},{N}): ' + ('VALID' if bad is None else 'INVALID '+bad), flush=True)
        if bad is None and outdir:
            v = 0; out = []
            for c in T: out.append('%x' % v); v ^= 1 << c
            open(f'{outdir}/efam_{n}_{k}_{N}.txt', 'w').write(f'# n {n} k {k} N {N} coil from the EXPLICIT even-line family l={l} (theory/struct/even/evenfam.py, S166); transition word: '+' '.join(map(str, T))+'\n'+'\n'.join(out)+'\n')
