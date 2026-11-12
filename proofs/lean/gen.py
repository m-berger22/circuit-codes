#!/usr/bin/env python3
# gen.py CODEFILE n k [L]  -> Lean source (stdout) proving IsMaxLength n k N via the verified checker
# (transition word packed into one natural number, 16 bits per step) + Lemma 1 at window length L.
import sys, os
f, n, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
v = [int(t,16) for line in open(f) if not line.startswith('#') for t in line.split()]
N = len(v)
T = []
for i in range(N):
    x = v[i] ^ v[(i+1) % N]
    assert x and x & (x-1) == 0
    T.append(x.bit_length()-1)
assert max(T) < n < 65536
W = sum(c << (16*i) for i, c in enumerate(T))
L = int(sys.argv[4]) if len(sys.argv) > 4 else (2*k+2 if k % 2 else 2*k+1)
tag = f"{n}_{k}"
B = int(os.environ.get('BLK', max(1, 20000 // N)))
print(f"""
def W_{tag} : ℕ := 0x{W:x}

def f_{tag} (i : ℕ) : ℕ := (W_{tag} >>> (16 * i)) &&& 0xFFFF

theorem ok_{tag}_0 : ∀ t < 0, okAt f_{tag} {n} {k} {N} t = true := allRange_zero
""")
a = 0
while a < N:
    m = min(B, N - a)
    print(f"""theorem blk_{tag}_{a} : allRange (okAt f_{tag} {n} {k} {N}) {a} {m} = true := by decide +kernel
theorem ok_{tag}_{a+m} : ∀ t < {a+m}, okAt f_{tag} {n} {k} {N} t = true := allRange_extend ok_{tag}_{a} blk_{tag}_{a}""")
    a += m
# S175: decide +kernel over the M range hits kernel deep recursion at N ~ 2300 (K_856_559)
LAST = "(by decide +kernel)" if N < 2000 else "(by intro M h1 h2 h3; refine ⟨by norm_num, by omega, by norm_num, by omega, ?_⟩; norm_num; nlinarith)"
print(f"""
theorem coil_{tag} : ∃ v : ℕ → Fin {n} → Bool, IsCoil {k} {N} v :=
  exists_coil_of_check f_{tag} {k} {N} (by norm_num) ok_{tag}_{N} (by decide +kernel)

/-- K({n},{k}) = {N}  (= 4k+2l+{N-4*k-2*(2*n-3*k-1)}, l = {2*n-3*k-1}; code: {f.split('/')[-1]}) -/
theorem K_{tag} : IsMaxLength {n} {k} {N} :=
  isMaxLength_of_chord coil_{tag} (by norm_num) {L} (by norm_num) (by norm_num) {LAST}
""")
