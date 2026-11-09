# Search programs (research code)
Compile: `gcc -O3 -march=native -o X X.c` for each.
- `cc.c`: windowed rerouting. `cc n k seed iters [infile]`; env SECS, OUT (best code file), NODES, LMIN, LMAX (see top of file).
- `sym.c`: the same with all images under v -> rot(v) XOR t rerouted together. `sym n k c seed iters [infile]`; env RWANT.
- `exh.c`: exhaustive search over cycles invariant under rot(v) XOR t (one class per t).
- `exhg.c`: exhaustive search for any coordinate-permutation cycle type: env SIGMA="6,3,2" etc.
- `check.py` (O(N^2), python) and `checkfast.c` (O(N x ball), coils) are the two earlier independent checkers.
Outputs of the exhaustive programs list per-class maxima; `expand.py` / `expandg.py` rebuild full codes from them (then re-checked).
