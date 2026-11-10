# Search programs (research code)
Compile: `gcc -O3 -march=native -o X X.c` for each.
- `cc.c`: windowed rerouting. `cc n k seed iters [infile]`; env SECS, OUT (best code file), NODES, LMIN, LMAX (see top of file).
- `sym.c`: the same with all images under v -> rot(v) XOR t rerouted together. `sym n k c seed iters [infile]`; env RWANT.
- `sym140.c` (2026-11-09): sym.c with env NOFULL=1 (skip the internal O(N^2) re-check at saves) and a 2^24 length cap;
  used for spread 3 n = 27..30 and spread 4, 5 n >= 26 with RWANT=2n BGREEDY=0.3 NODES=2000 SHRINK=0.05 WSLK=2 LB=40.
- `exh.c`: exhaustive search over cycles invariant under rot(v) XOR t (one class per t).
- `exhg.c`: exhaustive search for any coordinate-permutation cycle type: env SIGMA="6,3,2" etc.
- `exhr2.c` (2026-11-10): exhaustive search in a reflection class: `exhr2 n k m A|B` (m coordinate swaps; A = h fixes two
  cycle vertices, B = h flips two cycle edges); prints the best cycle on a `code` line. env MAXNODES.
- `exhs.c` (2026-11-10): the same search for snakes (open paths, no closure): `exhs n k m A|B`.
- `refl.c` (2026-11-10): rerouting local search inside a reflection class, started from an `exhr2` output:
  `refl n k m A|B infile`; env SECS NODES WMAX SEED OUT SHRINK.
- `refls.c` (2026-11-10): the snake version of refl.c, started from an `exhs` output: `refls n k m A|B infile`.
- `check.py` (O(N^2), python) and `checkfast.c` (O(N x ball), coils) are the two earlier independent checkers;
  `checkhash.c` (`checkhash file n k`, coils, O(N x ball) with a hash table, memory O(N)) is the third, for n >= 29.
Outputs of the exhaustive programs list per-class maxima; `expand.py` / `expandg.py` rebuild full codes from them (then re-checked).
