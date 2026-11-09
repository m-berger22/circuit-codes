# expand.py EXHFILE n k OUTPREFIX : take every t-line with the max bestN in an exh/exhb output file, rebuild the full cycle
# (v_{i+L} = rot1(v_i)^t from the printed segment) and write OUTPREFIX_t<hex>.txt in sym.c format. Validate with ../check.py.
import sys
f, n, k, pre = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
M = (1<<n)-1; rot = lambda v: ((v<<1)|(v>>(n-1))) & M
lines = open(f).read().splitlines(); best = []; mx = 0
for i, l in enumerate(lines):
    if l.startswith('t '):
        w = l.split(); N = int(w[5])
        if N and i+1 < len(lines) and lines[i+1].strip().startswith('seg'):
            seg = [int(x,16) for x in lines[i+1].split()[1:]]
            if N > mx: mx, best = N, []
            if N == mx: best.append((int(w[1],16), int(w[3]), seg))
for t, R, seg in best[:int(sys.argv[5]) if len(sys.argv) > 5 else 3]:
    L = len(seg); cyc = list(seg)
    while len(cyc) < R*L: cyc.append(rot(cyc[-L]) ^ t)
    assert rot(cyc[-L]) ^ t == cyc[0] and len(set(cyc)) == len(cyc)
    fn = '%s_t%x.txt' % (pre, t)
    with open(fn, 'w') as o:
        o.write('# n %d k %d N %d sym c 1 R %d L %d t %x (exh)\n' % (n, k, len(cyc), R, L, t))
        o.write(' '.join('%x' % v for v in cyc) + '\n')
    print(fn, len(cyc))
