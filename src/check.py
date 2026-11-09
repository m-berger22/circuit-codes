# independent O(N^2) checker for a spread-k circuit code file (hex vertices). usage: check.py file n k
import sys
f, n, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
OPEN = len(sys.argv) > 4 and sys.argv[4] == 'open'   # k-snake (path); length = #edges
v = [int(t,16) for line in open(f) if not line.startswith('#') for t in line.split()]
N = len(v)
assert OPEN or N >= 2*k, "too short"
assert all(0 <= x < 2**n for x in v), "out of range"
assert len(set(v)) == N, "repeated vertex"
for i in range(N - (1 if OPEN else 0)):
    assert bin(v[i]^v[(i+1)%N]).count('1') == 1, f"not an edge at {i}"
bad = 0
for i in range(N):
    for j in range(i+1, N):
        dc = (j-i) if OPEN else min(j-i, N-(j-i)); dh = bin(v[i]^v[j]).count('1')
        if (dc < k and dh != dc) or (dc >= k and dh < k): bad += 1
print(f"{f}: {'SNAKE length(edges)='+str(N-1) if OPEN else 'COIL'} n={n} k={k} N={N} {'VALID' if bad==0 else 'INVALID (%d bad pairs)'%bad}")
