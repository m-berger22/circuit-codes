# expandg.py EXHGFILE n k OUTPREFIX [maxcodes] : like expand.py but for exhg output (sigma read from the '# n .. sigma S' line,
# or env SIGMA). Rebuilds v_{i+L} = sigma(v_i)^t and writes OUTPREFIX_t<hex>.txt; validate with ../check.py.
import sys, os
f, n, k, pre = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
lines = open(f).read().splitlines()
sg = os.environ.get('SIGMA')
for l in lines:
    if l.startswith('# n ') and ' sigma ' in l: sg = l.split(' sigma ')[1].split()[0]
cyc_t = [n] if sg in (None, 'rot') else [int(x) for x in sg.split(',')]
perm = {}; pos = 0
for c in cyc_t:
    for i in range(c): perm[pos+i] = pos + (i+1) % c
    pos += c
assert pos == n
sig = lambda v: sum(1 << perm[b] for b in range(n) if v >> b & 1)
best = []; mx = 0
for i, l in enumerate(lines):
    if l.startswith('t '):
        w = l.split(); N = int(w[5])
        if N and i+1 < len(lines) and lines[i+1].strip().startswith('seg'):
            seg = [int(x,16) for x in lines[i+1].split()[1:]]
            if N > mx: mx, best = N, []
            if N == mx: best.append((int(w[1],16), int(w[3]), seg))
for t, R, seg in best[:int(sys.argv[5]) if len(sys.argv) > 5 else 3]:
    L = len(seg); cyc = list(seg)
    while len(cyc) < R*L: cyc.append(sig(cyc[-L]) ^ t)
    assert sig(cyc[-L]) ^ t == cyc[0] and len(set(cyc)) == len(cyc)
    fn = '%s_t%x.txt' % (pre, t)
    with open(fn, 'w') as o:
        o.write('# n %d k %d N %d sym sigma %s R %d L %d t %x (exhg)\n' % (n, k, len(cyc), sg, R, L, t))
        o.write(' '.join('%x' % v for v in cyc) + '\n')
    print(fn, len(cyc))
