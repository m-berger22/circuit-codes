# The odd-K second-step family fam(n) (pfam4.py) is a spread-6n path of length 26n+7: proof for all n >= 2  (S179)

**Theorem.** Let n >= 2, K = 6n+1, k = K-1 = 6n, d = 10n+2, and let T = fam(n) = P0 P1 P2 P3 P4 (pfam4.py =
pfam4_raw.build(n, (1,'f',1,0,0,1,0,0)); Section 1), a word of length L = 4K + 2n+3 = 26n+7 = (13K+8)/3 over d
coordinates. Then T is the transition word of a spread-k path in Q_d: for all 0 <= s <= p <= L, with
odd[s,p) = number of coordinates occurring an odd number of times in T[s..p-1] (= d_H(v_s, v_p)),

    p - s < k   implies   odd[s,p) = p - s,          p - s >= k   implies   odd[s,p) >= k.

Status: **complete for all n >= 2** (no separately verified small cases; n = 1 is outside the family). Every statement,
table entry and case inequality is tested against the words for n = 2..10 (Section 9); the case tables of Section 5
are in addition verified for ALL n in exact arithmetic (certificates + exhaustiveness). Honest limits: Section 7
("kind of evidence") -- in particular the State Table derivation is only sketched in prose (the table itself is tested
for every prefix), and "S = linear form on the case" is exact only inside the generator derive.py (numeric elsewhere).

Method: identical to PROOF_family_second.md (even-K sister family); read that document for the longer
explanations. Differences: (a) K is odd; (b) the cut vertices form a near-simplex with THREE exceptional pairs and one
short pair: D_02 = K-1, D_04 = D_13 = D_24 = K+1, all other D_jj' = K; (c) the "triples" 13_1, 02_1, 13_2, .., 13_n
are shifted (offset 2i in P0, 2i+1 in P1 and P2); (d) several index sets run downwards (03 in P2, P3, tail; 14 in P3;
12 in the tail), so the State Table is written with integer intervals and ONE rule for the terms.

**Parity remark** (difference (a)). odd[s,p) and p - s have the same parity. Since k is even, a window of odd length
w >= k automatically has odd >= k+1 = K once odd >= k is known. So the statement to prove is exactly the one above
(odd >= k = K-1 for all windows of length >= k); nothing extra is needed for odd lengths. In terms of the Near-Simplex
Lemma (odd = D + S) the claim for non-adjacent pieces is S >= K-1-D, i.e. S >= 0 for the pair (0,2), S >= -2 for
(0,4), (1,3), (2,4), and S >= -1 for (0,3), (1,4).

---------------------------------------------------------------------------------------------------------------------

## 1. The word (derived from pfam4_raw.py; the code is the definition)

Coordinates: (tau, i), tau a 2-subset of {0,..,4}, written tau_i. The **big** types 14, 34 have i = 1..n+1, the
other eight types have i = 1..n. So d = 2(n+1) + 8n = 10n+2.

T = P0 P1 P2 P3 P4; P0..P3 ("pieces") have length K = 6n+1, P4 = "the tail" has length 2n+3. Zones of P0..P3:

    zone 0 = offsets [0, 2n+2),     zone 1 = offsets [2n+2, 4n+2),     zone 2 = offsets [4n+2, 6n+1),

the tail is one zone "T". Inside a zone starting at z0: even column m = offset z0 + 2m, odd column m = offset
z0 + 2m+1. Zone 0: m = 0..n. Zone 1: m = 0..n-1. Zone 2: even columns m = 0..n-1, odd columns m = 0..n-2 (the zone has
2n-1 offsets; its last offset 6n is even column n-1). Tail: even columns m = 0..n+1, odd columns m = 0..n.
X_m denotes the "triple letter": X_0 = 13_1, X_1 = 02_1, X_m = 13_m for m >= 2.

**Zone-column table** (letter at even column m ‖ at odd column m; entries without condition hold for all m):

| piece | zone 0 (m = 0..n) | zone 1 (m = 0..n-1) | zone 2 (even m = 0..n-1, odd m = 0..n-2) |
|---|---|---|---|
| P0 | X_m ‖ 14_{m+1} (m<n), 12_1 (m=n) | 03_1 (m=0), 02_2 (m=1), 03_m (m>=2) ‖ 04_1 (m=0), 12_{m+1} (m>=1) | 02_{m+3} (m<n-2), 03_n (m=n-2), 14_{n+1} (m=n-1) ‖ 04_{m+2} |
| P1 | 23_{m+1} (m<n), 01_1 (m=n) ‖ X_m | 14_1 (m=0), 02_2 (m=1), 14_m (m>=2) ‖ 24_{m+1} | 02_{m+3} (m<n-2), 14_n (m=n-2), 14_{n+1} (m=n-1) ‖ 01_{m+2} |
| P2 | 34_1 (m=0), 03_{n+1-m} (m>=1) ‖ X_m | 34_{m+2} ‖ 24_{m+1} | 12_{m+1} ‖ 02_{m+3} (m<n-2), 02_2 (m=n-2) |
| P3 | 14_{n+1} (m=0), 03_{n+1-m} (m>=1) ‖ 04_n (m=0), 04_m (1<=m<n), 23_1 (m=n) | 13_1 (m=0), 23_{m+1} (m>=1) ‖ 24_{m+1} | 14_{n-m} ‖ 13_{m+2} |
| tail | 02_1 (m=0), 04_n (m=1), 12_{n+2-m} (m>=2) ‖ 01_1 (m=0), 03_{n+1-m} (m>=1) | | |

How it was read off pfam4_raw.py with OPT = (oS, p04, o12t, o14a, o23, o14b, o13, o12p) = (1,'f',1,0,0,1,0,0):
oS = 1 reverses sig (03_{n+1-i} at rows 2i of P2, P3 and 2i+1 of the tail); p04 = 'f' puts 04_n at tail row 2;
o12t = 1 gives 12_n, .., 12_1 at the tail rows 4, .., 2n+2; o14b = 1 gives 14_{n+1-i} at the P3 rows 4n+2i and 14_1 at
row 6n; all other orders are increasing. Rows 0, 1 and the n blocks (2i, 2i+1) are zone 0; rows 2n+2, 2n+3 and the
builder's "zone 2" (n-1 row pairs) are zone 1 here; the builder's "zone 3" and the last row 6n are zone 2 here.
[test_states.py: positions.column (this table) = the builder's word, every letter, n = 2..10.]

**(O) Position table** (offset of tau_i in each piece that contains it; closed forms, positions.pos_table):

| piece | positions |
|---|---|
| P0 | 13_1: 0;  13_i (i>=2): 2i;  02_1: 2;  02_2: 2n+4;  02_i (i>=3): 4n+2i-4;  14_i (i<=n): 2i-1;  14_{n+1}: 6n;  12_1: 2n+1;  12_i (i>=2): 2n+2i+1;  03_1: 2n+2;  03_i (2<=i<=n-1): 2n+2i+2;  03_n: 6n-2;  04_1: 2n+3;  04_i (i>=2): 4n+2i-1 |
| P1 | 23_i: 2i-2;  01_1: 2n;  01_i (i>=2): 4n+2i-1;  13_1: 1;  13_i (i>=2): 2i+1;  02_1: 3;  02_2: 2n+4;  02_i (i>=3): 4n+2i-4;  14_1: 2n+2;  14_i (2<=i<=n-1): 2n+2i+2;  14_n: 6n-2;  14_{n+1}: 6n;  24_i: 2n+2i+1 |
| P2 | 34_1: 0;  34_i (i>=2): 2n+2i-2;  03_i: 2n+2-2i;  13_1: 1;  13_i (i>=2): 2i+1;  02_1: 3;  02_2: 6n-1;  02_i (i>=3): 4n+2i-3;  24_i: 2n+2i+1;  12_i: 4n+2i |
| P3 | 14_{n+1}: 0;  14_i (i<=n): 6n+2-2i;  03_i: 2n+2-2i;  04_n: 1;  04_i (i<n): 2i+1;  23_1: 2n+1;  23_i (i>=2): 2n+2i;  13_1: 2n+2;  13_i (i>=2): 4n+2i-1;  24_i: 2n+2i+1 |
| tail | 02_1: 0;  01_1: 1;  04_n: 2;  12_i: 2n+4-2i;  03_i: 2n+3-2i |

[test_slots.py: this table = the word, n = 2..10.]

**(P) Incidence.** For j = 0..3: every tau_i with exactly one of j, j+1 in tau occurs exactly once in P_j, and nothing
else occurs in P_j (each row of (O) lists six types with every index once). The tail consists of the 2n+3 pairwise
distinct letters 02_1, 01_1, 04_n, 12_1..12_n, 03_1..03_n. In particular the letters of one piece are pairwise
distinct. [test_states.py]

---------------------------------------------------------------------------------------------------------------------

## 2. The Near-Simplex Lemma

sigma_{jj'}(tau) = -1 if tau separates j, j' (exactly one of j, j' in tau), +1 otherwise. Every position 0 <= p <= L is
uniquely p = jK + e with (0 <= j <= 3, 0 <= e < K) or (j = 4, 0 <= e <= 2n+3). Pre_j(e) = set of the first e letters
of P_j.

**Near-Simplex Lemma.** For p = jK+e, p' = j'K+e', j < j':

    odd[p,p') = D_jj' + S_{jj'}(e,e'),     S_{jj'}(e,e') := sum over c in Pre_j(e) symdiff Pre_j'(e') of sigma_{jj'}(c),

    D_02 = K-1,   D_04 = D_13 = D_24 = K+1,   D_jj' = K for the other six pairs.

*Proof.* As in PROOF_family_second.md Section 2: by (P), v_{jK} xor v_{j'K} = {tau_i : tau separates j, j'}; six types separate
j, j' ({j,w}, {j',w} for the three other w), each with n coordinates plus one for each big type among them. The big
types 14, 34 are both among the six for (0,4) (01,02,03,14,24,34), (1,3) (01,12,14,03,23,34), (2,4)
(02,12,23,04,14,34): 6n+2 = K+1. Neither is among them for (0,2) (01,03,04,12,23,24): 6n = K-1. Exactly one for
(0,1): 14; (0,3): 34; (1,2): 14; (2,3): 34; (1,4): 34; (3,4): 14: 6n+1 = K. The rest is
|Dset xor X| = |Dset| + #{c in X not in Dset} - #{c in X in Dset} with X = Pre_j(e) symdiff Pre_j'(e'). QED
[test_simplex.py]

**Per-type form.** (S)  S = sum over types of sigma_{jj'}(tau) * n_tau,  n_tau = |I_j,tau(e) symdiff I_j',tau(e')|
(u_tau / w_tau if tau occurs only in the first / second piece).

---------------------------------------------------------------------------------------------------------------------

## 3. The State Table

**Local coordinates.** e = z0 + r (z0 = start of the zone, r = offset inside the zone; tail: r = e), a = ceil(r/2),
b = floor(r/2).

**(E) Domain facts** (r -> (a,b) is a bijection onto the integer pairs with these facts):

    all zones:   b >= 0,   a >= b,   a <= b+1;
    zone 0:      b <= n          (r <= 2n+1);
    zone 1:      b <= n-1        (r <= 2n-1);
    zone 2:      a <= n-1        (r <= 2n-2);
    tail:        b <= n+1        (r <= 2n+3);
    and          n >= 2.

**(R0)** Pre_j(e) = all letters of the zones before z, the even columns m <= a-1 and the odd columns m <= b-1 of zone z.

**State Table** (generated from states.py; [cond] = 1/0; every set is a union of integer intervals {lo..hi}, empty
if hi < lo; types not listed never occur in the piece):

<!--STATES-->
| piece, zone | index sets I_tau of the prefix with local coordinates (a, b)  ({lo..hi} is empty if hi < lo) |
|---|---|
| P0, z=0 | 13: {1..[a≥1]} + {2..a-1};  02: {1..[a≥2]};  14: {1..min(b,n)};  12: -;  03: -;  04: - |
| P0, z=1 | 13: {1..n};  02: {1..1+[a≥2]};  14: {1..n};  12: {1..max(b,1)};  03: {1..[a≥1]} + {2..a-1};  04: {1..[b≥1]} |
| P0, z=2 | 13: {1..n};  14: {1..n};  12: {1..n};  02: {1..min(a+2,n)};  03: {1..n-1+[a≥n-1]};  04: {1..b+1} |
| P1, z=0 | 23: {1..min(a,n)};  01: {1..[a≥n+1]};  13: {1..[b≥1]} + {2..b-1};  02: {1..[b≥2]};  14: -;  24: - |
| P1, z=1 | 23: {1..n};  01: {1..1};  13: {1..n};  02: {1..1+[a≥2]};  14: {1..[a≥1]} + {2..a-1};  24: {1..b} |
| P1, z=2 | 23: {1..n};  13: {1..n};  24: {1..n};  02: {1..min(a+2,n)};  14: {1..n-1+[a≥n-1]};  01: {1..b+1} |
| P2, z=0 | 34: {1..[a≥1]};  03: {n+2-a..n};  13: {1..[b≥1]} + {2..b-1};  02: {1..[b≥2]};  24: -;  12: - |
| P2, z=1 | 34: {1..a+1};  03: {1..n};  13: {1..n};  02: {1..1};  24: {1..b};  12: - |
| P2, z=2 | 34: {1..n+1};  03: {1..n};  13: {1..n};  24: {1..n};  12: {1..a};  02: {1..1} + {3..min(b+2,n)} + {2..1+[b≥n-1]} |
| P3, z=0 | 14: {n+1..n+[a≥1]};  03: {n+2-a..n};  04: {n..n-1+[b≥1]} + {1..b-1};  23: -;  13: -;  24: - |
| P3, z=1 | 14: {n+1..n+1};  03: {1..n};  04: {1..n};  23: {1..max(a,1)};  13: {1..[a≥1]};  24: {1..b} |
| P3, z=2 | 14: {n+1-a..n+1};  03: {1..n};  04: {1..n};  23: {1..n};  24: {1..n};  13: {1..b+1} |
| tail (zone T) | 02: {1..[a≥1]};  04: {n..n-1+[a≥2]};  12: {n+3-a..n};  01: {1..[b≥1]};  03: {n+2-b..n} |
<!--/STATES-->

Derivation: apply (R0) to the zone-column table. Examples of the less obvious entries.
P0 zone 0, 13: X_0 = 13_1 iff a >= 1, X_m = 13_m for 2 <= m <= a-1; 02: X_1 = 02_1 iff a >= 2; 14_{m+1} for
m <= min(b-1, n-1). P0 zone 1: 03_1 iff a >= 1, 03_m for 2 <= m <= a-1; 02 = {1} + {2} iff a >= 2;
12 = {1} + {2..b} = {1..max(b,1)}. P0 zone 2: 02_{m+3} for m <= min(a-1, n-3): 02 = {1..min(a+2,n)}; 03_n at even
column n-2, iff a >= n-1; 14_{n+1} (even column n-1) is never inside a zone-2 prefix (a <= n-1); 04 = {1} + {2..b+1}.
P1 zone 2: the same with 14_n in place of 03_n. P2 zone 0: 03_{n+1-m} for 1 <= m <= a-1 = {n+2-a..n}.
P2 zone 2: 02 = {1} + {3..min(b+2,n)} (odd columns m <= min(b-1, n-3)) + {2} iff b >= n-1 (odd column n-2).
P3 zone 0: 04_n iff b >= 1, 04_m for 1 <= m <= b-1 (m < n holds because b <= n). P3 zone 2: 14 = {n+1} + {n+1-a..n}.
Tail: 04_n iff a >= 2; 12_{n+2-m} for 2 <= m <= a-1 = {n+3-a..n}; 03_{n+1-m} for 1 <= m <= b-1 = {n+2-b..n}.
[test_states.py: the table = the index sets of every prefix of every piece and the tail, n = 2..10, including
1 <= lo, hi <= number of indices and disjointness of the intervals of an entry.]

---------------------------------------------------------------------------------------------------------------------

## 4. Adjacent pieces: the Slot Lemma

Window from offset e of P_j to offset e' of P_{j+1} (j = 0..3; for j = 3: 0 <= e' <= 2n+3), length w = K - e + e'.
With p_c, q_c the offsets of a common letter c in P_j, P_{j+1}:

    (A1)   odd = w - 2 C_j(e,e'),        C_j(e,e') := #{common c : p_c >= e and q_c < e'}.

**Slot Lemma** (as in PROOF_family_second.md Section 4). If every common letter c has a 2-element set Phi_c inside [p_c, q_c+1] and
the Phi_c are pairwise disjoint, then (A2) C_j(e,e') <= max(0, floor((e'-e+1)/2)).

**Slot Table** (positions from (O); common types: 13, 14, 02 / 13, 24, 02 / 13, 03, 24; P3 and tail: 04_n and 03_i):

| pieces | common letter c: (p_c -> q_c), Phi_c |
|---|---|
| P0, P1 | 13_1: (0 -> 1), {0,1};  02_1: (2 -> 3), {2,3};  13_i (i>=2): (2i -> 2i+1), {2i, 2i+1};  14_1: (1 -> 2n+2), {2n+2, 2n+3};  02_2: (2n+4 -> 2n+4), {2n+4, 2n+5};  14_i (2<=i<=n-1): (2i-1 -> 2n+2i+2), {2n+2i+2, 2n+2i+3};  02_i (i>=3): (4n+2i-4 -> 4n+2i-4), {4n+2i-4, 4n+2i-3};  14_n: (2n-1 -> 6n-2), {6n-2, 6n-1};  14_{n+1}: (6n -> 6n), {6n, 6n+1} |
| P1, P2 | 13_1: (1 -> 1), {1,2};  02_1: (3 -> 3), {3,4};  13_i (i>=2): (2i+1 -> 2i+1), {2i+1, 2i+2};  24_i: (2n+2i+1 -> 2n+2i+1), {2n+2i+1, 2n+2i+2};  02_i (i>=3): (4n+2i-4 -> 4n+2i-3), {4n+2i-3, 4n+2i-2};  02_2: (2n+4 -> 6n-1), {6n-1, 6n} |
| P2, P3 | 13_1: (1 -> 2n+2), {1, 2n+2};  03_i: (2n+2-2i -> 2n+2-2i), {2n+2-2i, 2n+3-2i};  24_i: (2n+2i+1 -> 2n+2i+1), {2n+2i+1, 2n+2i+2};  13_i (i>=2): (2i+1 -> 4n+2i-1), {4n+2i-1, 4n+2i} |
| P3, tail | 04_n: (1 -> 2), {1,2};  03_i: (2n+2-2i -> 2n+3-2i), {2n+3-2i, 2n+4-2i} |

Each Phi_c is a 2-subset of [p_c, q_c+1], and the sets are disjoint because they tile these ranges:
P0,P1: {0..2n+1} (13, 02_1), {2n+2, 2n+3}, {2n+4, 2n+5}, {2n+6..4n+1} (14_i, i = 2..n-1), {4n+2..6n-3} (02_i, i = 3..n),
{6n-2, 6n-1}, {6n, 6n+1}.  P1,P2: {1..2n+2}, {2n+3..4n+2} (24), {4n+3..6n-2} (02_i, i = 3..n), {6n-1, 6n}.
P2,P3: {1, 2n+2}, {2..2n+1} (03), {2n+3..4n+2} (24), {4n+3..6n} (13_i, i = 2..n).  P3,tail: {1,2}, {3..2n+2}.
[test_slots.py]

**Corollary A.** The path property holds for every window between adjacent pieces (incl. P3 and the tail).
*Proof.* C = 0: odd = w. C >= 1: e'-e+1 >= 2C >= 2 by (A2), so w = K+e'-e >= K+1 > k and
odd = K + (e'-e) - 2C >= K-1 = k. QED  (The parity of K plays no role here.) [test_slots.py]

---------------------------------------------------------------------------------------------------------------------

## 5. Non-adjacent pieces

**Proposition B.** For all prefixes e of P_j and e' of P_j' (tail: 0 <= e' <= 2n+3):
S_02 >= 0;   S_04, S_13, S_24 >= -2;   S_03, S_14 >= -1.   (Equivalently D_jj' + S >= K-1 in all six pairs.)

Local coordinates (z; a, b) for the start prefix, (z'; A, B) for the end prefix.

**Rule (R) for the terms.** For two unions of disjoint intervals X = U [lo_i, hi_i], Y = U [LO_j, HI_j]:

    |X symdiff Y| = |X| + |Y| - 2 |X cap Y|,   |[lo,hi]| = pos(hi-lo+1),   |[lo,hi] cap [LO,HI]| = pos(min(hi,HI) - max(lo,LO) + 1),

pos(x) = max(x,0). terms.py applies (R) mechanically to the State Table (pos is omitted where the bound is visibly
>= 0, e.g. for {1..[cond]}); the strings are printed below, evaluated on the words by test_rows.py, and evaluated
symbolically by derive.py.

**The case tables** are of the same kind as in PROOF_family_second.md Section 5: each case = linear conditions in n, a, b, A, B;
on the case S equals the linear form in column "S"; the last column is a certificate S - lb = sum of multiples
(1..4) of expressions that are >= 0 on the case: domain facts (E) of the start zone [(b), (a-b), (-a+b+1), and
(n-b) / (n-b-1) / (n-a-1)], of the end zone [(B), (A-B), (-A+B+1), and (n-B) / (n-B-1) / (n-A-1) / (n-B+1)], (n-2),
or a condition of the case. They were generated by derive.py (exact symbolic case splitting, Farkas certificates in
rational arithmetic; see PROOF_family_second.md Section 5 for the description of the procedure).

<!--ROWS-->
**Pair (0,2).**  odd = K-1 + S,   S = n02 + n13 + u14 + w34 − n03 − u04 − n12 − w24   (to show: S ≥ 0)

*Zones (0,0).*  n02 = [a≥2]+[B≥2]-2·(pos(min([a≥2],[B≥2]))),  n13 = [a≥1]+pos(a-1-(2)+1)+[B≥1]+pos(B-1-(2)+1)-2·(pos(min([a≥1],[B≥1]))+pos(min([a≥1],B-1)-(max(1,2))+1)+pos(min(a-1,[B≥1])-(max(2,1))+1)+pos(min(a-1,B-1)-(2)+1)),  u14 = pos(min(b,n)),  w34 = [A≥1],  n03 = pos(n-(n+2-A)+1),  u04 = 0,  n12 = 0,  w24 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 3, B ≥ a | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| B ≥ 2, a ≥ B+1 | a+b-A-B+2 | 2 | S−2 = (-a+b+1) + (-A+B+1) + 2·(a-B-1) |
| B ≥ 2, a ≤ 0 | b-A+B+2 | 1 | S−1 = (b) + (-A+B+1) |
| a ≥ 2, A ≤ 0 | a+b | 3 | S−3 = (-a+b+1) + 2·(a-2) |
| a ≤ 0, A ≤ 0 | b | 0 | S = (b) |
| a = 2, B ≥ 2 | -3·a+b-A+B+6 | 0 | S = (-a+b+1) + (-A+B+1) + 2·(-a+2) |
| a ≥ 2, B ≤ 0, A ≥ 1 | a+b-A+2 | 4 | S−4 = (-a+b+1) + (-A+B+1) + 2·(a-2) + (-B) |
| B = 1, a ≥ 3 | a+b-A+1 | 4 | S−4 = (-a+b+1) + (-A+B+1) + (-B+1) + 2·(a-3) |
| B = 1, a ≤ 0 | b-A+3 | 1 | S−1 = (b) + (-A+B+1) + (-B+1) |
| a = 1, B ≥ 2 | b-A+B+1 | 0 | S = (b) + (-A+B+1) |
| a = 1, A ≤ 0 | b+1 | 1 | S−1 = (b) |
| a ≤ 0, B ≤ 0, A ≥ 1 | b-A+2 | 1 | S−1 = (b) + (-A+B+1) + (-B) |
| a = 2, B = 1 | -a+b-A+5 | 2 | S−2 = (-a+b+1) + (-A+B+1) + (-B+1) |
| a = 1, B ≤ 0, A ≥ 1 | b-A+3 | 2 | S−2 = (b) + (-A+B+1) + (-B) |
| a = 1, B = 1 | b-A+2 | 0 | S = (b) + (-A+B+1) + (-B+1) |

*Zones (0,1).*  n02 = [a≥2]+1-2·(pos(min([a≥2],1))),  n13 = [a≥1]+pos(a-1-(2)+1)+n-2·(pos(min([a≥1],n))+pos(min(a-1,n)-(max(2,1))+1)),  u14 = pos(min(b,n)),  w34 = pos(A+1),  n03 = n,  u04 = 0,  n12 = 0,  w24 = pos(B)

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2 | -a+b+A-B+2 | 1 | S−1 = (-a+b+1) + (A-B) |
| a ≤ 0 | b+A-B+2 | 2 | S−2 = (b) + (A-B) |
| a = 1 | b+A-B+1 | 1 | S−1 = (b) + (A-B) |

*Zones (0,2).*  n02 = [a≥2]+1+pos(min(B+2,n)-(3)+1)+pos(1+[B≥n-1]-(2)+1)-2·(pos(min([a≥2],1))+pos(min([a≥2],min(B+2,n))-(max(1,3))+1)+pos(min([a≥2],1+[B≥n-1])-(max(1,2))+1)),  n13 = [a≥1]+pos(a-1-(2)+1)+n-2·(pos(min([a≥1],n))+pos(min(a-1,n)-(max(2,1))+1)),  u14 = pos(min(b,n)),  w34 = n+1,  n03 = n,  u04 = 0,  n12 = pos(A),  w24 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ B+2, a ≤ 0 | b-A+B+2 | 1 | S−1 = (b) + (-A+B+1) |
| a ≥ 2, n ≥ B+2 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| a ≥ 2, B ≥ n-1 | n-a+b-A+1 | 1 | S−1 = (-a+b+1) + (n-A-1) |
| B ≥ n-1, a ≤ 0 | n+b-A+1 | 2 | S−2 = (b) + (n-A-1) |
| a = 1, n ≥ B+2 | b-A+B+1 | 0 | S = (b) + (-A+B+1) |
| a = 1, B ≥ n-1 | n+b-A | 1 | S−1 = (b) + (n-A-1) |

*Zones (1,0).*  n02 = 1+[a≥2]+[B≥2]-2·(pos(min(1+[a≥2],[B≥2]))),  n13 = n+[B≥1]+pos(B-1-(2)+1)-2·(pos(min(n,[B≥1]))+pos(min(n,B-1)-(max(1,2))+1)),  u14 = n,  w34 = [A≥1],  n03 = [a≥1]+pos(a-1-(2)+1)+pos(n-(n+2-A)+1)-2·(pos(min([a≥1],n)-(max(1,n+2-A))+1)+pos(min(a-1,n)-(max(2,n+2-A))+1)),  u04 = [b≥1],  n12 = pos(max(b,1)),  w24 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| B ≥ 2, a ≤ 0 | 2·n-A-B+2 | 1 | S−1 = (-A+B+1) + 2·(n-B) |
| a ≥ 2, A ≥ n+1 | 2·n+a-b-A-B+2 | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-B) |
| a ≥ 2, A ≤ 0 | 2·n-a-b+2 | 3 | S−3 = (-a+b+1) + 2·(n-b-1) |
| B ≤ 1, a+A ≥ n+2 | a-b+A-1 | 2 | S−2 = (n-b-1) + (-n+a+A-2) |
| A ≤ 0, a ≤ 0 | 2·n | 4 | S−4 = 2·(n-2) |
| B ≥ 2, n ≥ A, a+A ≥ n+2 | a-b+A-B | 0 | S = (a-b) + (A-B) |
| a ≥ 2, B ≥ 2, n ≥ a+A-1 | 2·n-a-b-A-B+4 | 2 | S−2 = (a-b) + (A-B) + 2·(n-a-A+1) |
| a ≥ 2, B ≤ 1, A ≥ n | a-b+A-1 | 2 | S−2 = (n-b-1) + (a-2) + (-n+A) |
| a ≥ 2, B ≤ 0, A ≥ 1 | 2·n-a-b-A+4 | 4 | S−4 = (-a+b+1) + 2·(n-b-1) + (-A+B+1) + (-B) |
| a ≥ 1, A ≥ n+1, b ≤ 0 | 2·n-A-B+3 | 2 | S−2 = (-A+B+1) + 2·(n-B) |
| B = 1, a ≤ 0 | 2·n-A+1 | 3 | S−3 = (-A+B+1) + 2·(n-2) + (-B+1) |
| a ≤ 1, A ≥ n+1, b ≥ 1 | 2·n-b-A-B+3 | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-B) + (-a+1) |
| a ≤ 1, A ≤ 0, b ≥ 1 | 2·n-b-1 | 2 | S−2 = (n-b-1) + (n-2) |
| A ≤ 0, a ≥ 1, b ≤ 0 | 2·n-1 | 3 | S−3 = 2·(n-2) |
| B ≤ 0, A ≥ 1, a ≤ 0 | 2·n-A+2 | 5 | S−5 = (-A+B+1) + 2·(n-2) + (-B) |
| B ≥ 2, a ≥ 1, n ≥ A+1, b ≤ 0 | 2·n-A-B+1 | 3 | S−3 = (A-B) + 2·(n-A-1) |
| a ≥ 2, B ≥ 2, n = A | a-b+A-B | 0 | S = (a-b) + (A-B) |
| a ≥ 2, B = 1, n ≥ a+A-1 | 2·n-a-b-A+3 | 3 | S−3 = (n-b-1) + (n-a-A+1) |
| B ≤ 1, a ≥ 1, A ≥ n, b ≤ 0 | A | 2 | S−2 = (n-2) + (-n+A) |
| a ≤ 1, B ≥ 2, n ≥ A+1, b ≥ 1 | 2·n-b-A-B+1 | 2 | S−2 = (a-b) + (A-B) + (-a+1) + 2·(n-A-1) |
| a ≤ 1, B ≤ 1, A ≥ n, b ≥ 1 | -b+A | 1 | S−1 = (n-b-1) + (-n+A) |
| a ≤ 1, B ≤ 0, A ≥ 1, b ≥ 1 | 2·n-b-A+1 | 3 | S−3 = (n-b-1) + (-A+B+1) + (n-2) + (-B) |
| B ≤ 0, A ≥ 1, a ≥ 1, b ≤ 0 | 2·n-A+1 | 4 | S−4 = (-A+B+1) + 2·(n-2) + (-B) |
| B ≥ 2, a ≥ 1, n = A, b ≤ 0 | A-B+1 | 1 | S−1 = (A-B) |
| B = 1, a ≥ 1, n ≥ A+1, b ≤ 0 | 2·n-A | 3 | S−3 = (n-2) + (n-A-1) |
| a ≤ 1, B ≥ 2, n = A, b ≥ 1 | -b+A-B+1 | 0 | S = (a-b) + (A-B) + (-a+1) |
| a ≤ 1, B = 1, n ≥ A+1, b ≥ 1 | 2·n-b-A | 2 | S−2 = (n-b-1) + (n-A-1) |

*Zones (1,1).*  n02 = 1+[a≥2]+1-2·(pos(min(1+[a≥2],1))),  n13 = 0,  u14 = n,  w34 = pos(A+1),  n03 = [a≥1]+pos(a-1-(2)+1)+n-2·(pos(min([a≥1],n))+pos(min(a-1,n)-(max(2,1))+1)),  u04 = [b≥1],  n12 = pos(max(b,1)),  w24 = pos(B)

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2 | a-b+A-B | 0 | S = (a-b) + (A-B) |
| a ≤ 0 | A-B | 0 | S = (A-B) |
| a ≥ 1, b ≤ 0 | A-B+1 | 1 | S−1 = (A-B) |
| a ≤ 1, b ≥ 1 | -b+A-B+1 | 0 | S = (a-b) + (A-B) + (-a+1) |

*Zones (1,2).*  n02 = 1+[a≥2]+1+pos(min(B+2,n)-(3)+1)+pos(1+[B≥n-1]-(2)+1)-2·(pos(min(1+[a≥2],1))+pos(min(1+[a≥2],min(B+2,n))-(max(1,3))+1)+pos(min(1+[a≥2],1+[B≥n-1])-(max(1,2))+1)),  n13 = 0,  u14 = n,  w34 = n+1,  n03 = [a≥1]+pos(a-1-(2)+1)+n-2·(pos(min([a≥1],n))+pos(min(a-1,n)-(max(2,1))+1)),  u04 = [b≥1],  n12 = pos(max(b,1))+pos(A)-2·(pos(min(max(b,1),A))),  w24 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2, b ≥ A+1 | a-b+A+B | 0 | S = (a-b) + 2·(B) + (A-B) |
| a ≥ 2, B ≥ n-1 | n+a+b-A-3 | 1 | S−1 = (-a+b+1) + (n-A-1) + 2·(a-2) |
| B ≥ n-1, a ≤ 0 | n-A+1 | 2 | S−2 = (n-A-1) |
| a ≤ 1, b ≥ A+1 | -b+A+B+1 | 0 | S = (a-b) + 2·(B) + (A-B) + (-a+1) |
| a ≤ 0, A ≤ 0 | A+B | 0 | S = 2·(B) + (A-B) |
| n ≥ B+2, a ≤ 0, A ≥ 1 | -A+B+2 | 1 | S−1 = (-A+B+1) |
| a ≥ 2, n ≥ B+2, A ≥ b | a+b-A+B | 2 | S−2 = (-a+b+1) + (-A+B+1) + 2·(a-2) |
| a ≥ 1, b ≤ 0, A ≤ 0 | A+B+1 | 1 | S−1 = 2·(B) + (A-B) |
| B ≥ n-1, a ≥ 1, b ≤ 0 | n-A+2 | 3 | S−3 = (n-A-1) |
| a ≤ 1, B ≥ n-1, b ≥ 1 | n+b-A | 2 | S−2 = (n-A-1) + (b-1) |
| n ≥ B+2, a ≥ 1, b ≤ 0, A ≥ 1 | -A+B+3 | 2 | S−2 = (-A+B+1) |
| a ≤ 1, n ≥ B+2, b ≥ 1, A ≥ b | b-A+B+1 | 1 | S−1 = (-A+B+1) + (b-1) |

*Zones (2,0).*  n02 = pos(min(a+2,n))+[B≥2]-2·(pos(min(min(a+2,n),[B≥2]))),  n13 = n+[B≥1]+pos(B-1-(2)+1)-2·(pos(min(n,[B≥1]))+pos(min(n,B-1)-(max(1,2))+1)),  u14 = n,  w34 = [A≥1],  n03 = pos(n-1+[a≥n-1])+pos(n-(n+2-A)+1)-2·(pos(min(n-1+[a≥n-1],n)-(max(1,n+2-A))+1)),  u04 = pos(b+1),  n12 = n,  w24 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, A ≥ n+1 | 2·n+a-b-A-B+2 | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-B) |
| n ≥ a+2, A ≤ 0 | a-b+2 | 2 | S−2 = (a-b) |
| a ≥ n-1, A ≥ n+1 | 3·n-b-A-B+1 | 1 | S−1 = (a-b) + (n-a-1) + (-A+B+1) + 2·(n-B) |
| a ≥ n-1, A ≤ 0 | n-b-1 | 0 | S = (a-b) + (n-a-1) |
| n ≥ a+2, B ≥ 2, n ≥ A | a-b+A-B | 0 | S = (a-b) + (A-B) |
| n ≥ a+2, B ≥ 1, A ≤ 1 | a-b-A+3 | 2 | S−2 = (a-b) + (-A+1) |
| n ≥ a+2, B ≤ 1, A ≥ 2 | a-b+A-1 | 1 | S−1 = (a-b) + (A-2) |
| n ≥ a+2, B ≤ 0, A ≥ 1 | a-b-A+4 | 3 | S−3 = (a-b) + (-A+B+1) + (-B) |
| a ≥ n-1, B ≥ 2, n ≥ A | n-b+A-B-1 | 0 | S = (a-b) + (n-a-1) + (A-B) |
| a ≥ n-1, B = 1 | n-b+A-2 | 0 | S = (a-b) + (n-a-1) + (A-B) + (B-1) |
| a ≥ n-1, B ≤ 0, A ≥ 1 | n-b+A-1 | 1 | S−1 = (a-b) + (n-a-1) + (A-1) |

*Zones (2,1).*  n02 = pos(min(a+2,n))+1-2·(pos(min(min(a+2,n),1))),  n13 = 0,  u14 = n,  w34 = pos(A+1),  n03 = pos(n-1+[a≥n-1])+n-2·(pos(min(n-1+[a≥n-1],n))),  u04 = pos(b+1),  n12 = n,  w24 = pos(B)

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2 | a-b+A-B | 0 | S = (a-b) + (A-B) |
| a ≥ n-1 | n-b+A-B-1 | 0 | S = (a-b) + (n-a-1) + (A-B) |

*Zones (2,2).*  n02 = pos(min(a+2,n))+1+pos(min(B+2,n)-(3)+1)+pos(1+[B≥n-1]-(2)+1)-2·(pos(min(min(a+2,n),1))+pos(min(min(a+2,n),min(B+2,n))-(max(1,3))+1)+pos(min(min(a+2,n),1+[B≥n-1])-(max(1,2))+1)),  n13 = 0,  u14 = n,  w34 = n+1,  n03 = pos(n-1+[a≥n-1])+n-2·(pos(min(n-1+[a≥n-1],n))),  u04 = pos(b+1),  n12 = n+pos(A)-2·(pos(min(n,A))),  w24 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ B+2, B ≥ a | -a-b+A+B | 0 | S = (a-b) + (A-B) + 2·(-a+B) |
| n ≥ a+2, a ≥ B+1 | a-b+A-B | 0 | S = (a-b) + (A-B) |
| B ≥ n-1, a ≤ 0 | n-3·a-b+A-3 | 0 | S = (a-b) + (A-B) + 2·(n-2) + (-n+B+1) + 4·(-a) |
| a ≥ n-1, n ≥ B+3 | n-b+A-B-1 | 0 | S = (a-b) + (n-a-1) + (A-B) |
| n ≥ a+2, B ≥ n-1, a ≥ 1 | n-a-b+A-3 | 0 | S = (a-b) + (A-B) + 2·(n-a-2) + (-n+B+1) |
| a ≥ n-1, n = B+2 | -n-b+A+B+3 | 0 | S = (a-b) + (n-a-1) + (A-B) + 2·(-n+B+2) |
| a ≥ n-1, B ≥ n-1, n ≥ 3 | -b+A | 0 | S = (a-b) + (n-a-1) + (A-B) + (-n+B+1) |
| a ≥ n-1, B ≥ n-1, n ≤ 2 | -2·n-b+A+4 | 0 | S = (a-b) + (n-a-1) + (A-B) + (-n+B+1) + 2·(-n+2) |

**Pair (0,3).**  odd = K + S,   S = n03 + u12 + n14 + w24 − u02 − n04 − n13 − w23   (to show: S ≥ -1)

*Zones (0,0).*  n03 = pos(n-(n+2-A)+1),  u12 = 0,  n14 = pos(min(b,n))+pos(n+[A≥1]-(n+1)+1)-2·(pos(min(min(b,n),n+[A≥1])-(max(1,n+1))+1)),  w24 = 0,  u02 = [a≥2],  n04 = pos(n-1+[B≥1]-(n)+1)+pos(B-1),  n13 = [a≥1]+pos(a-1-(2)+1),  w23 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| B ≥ 1, a ≤ 0 | b+A-B | 0 | S = (b) + (A-B) |
| A ≤ 0, a ≤ 0 | b | 0 | S = (b) |
| A ≤ 0, b ≥ n | 2·n-a-b | -1 | S+1 = (-a+b+1) + 2·(n-b) |
| b ≥ n, B ≥ 1 | 2·n-a-b+A-B | -1 | S+1 = (-a+b+1) + 2·(n-b) + (A-B) |
| A ≥ 1, B ≤ 0, a ≤ 0 | b+A | 1 | S−1 = (b) + (A-1) |
| A ≥ 1, b ≥ n, B ≤ 0 | 2·n-a-b+A | 0 | S = (-a+b+1) + 2·(n-b) + (A-1) |
| n ≥ b+1, a ≥ 2, B ≥ 1 | -a+b+A-B | -1 | S+1 = (-a+b+1) + (A-B) |
| a = 1, B ≥ 1 | b+A-B-1 | -1 | S+1 = (b) + (A-B) |
| A ≤ 0, n ≥ b+1, a ≥ 2 | -a+b | -1 | S+1 = (-a+b+1) |
| A ≤ 0, a = 1 | b-1 | -1 | S+1 = (b) |
| A ≥ 1, n ≥ b+1, a ≥ 2, B ≤ 0 | -a+b+A | 0 | S = (-a+b+1) + (A-1) |
| A ≥ 1, a = 1, B ≤ 0 | b+A-1 | 0 | S = (b) + (A-1) |

*Zones (0,1).*  n03 = n,  u12 = 0,  n14 = pos(min(b,n))+pos(n+1-(n+1)+1)-2·(pos(min(min(b,n),n+1)-(max(1,n+1))+1)),  w24 = pos(B),  u02 = [a≥2],  n04 = n,  n13 = [a≥1]+pos(a-1-(2)+1)+[A≥1]-2·(pos(min([a≥1],[A≥1]))+pos(min(a-1,[A≥1])-(max(2,1))+1)),  w23 = pos(max(A,1))

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≤ 0, A ≥ 1 | b-A+B | -1 | S+1 = (b) + (-A+B+1) |
| a ≤ 0, A ≤ 0 | b+B | 0 | S = (b) + (B) |
| b ≥ n, A ≤ 0 | 2·n-a-b+B | -1 | S+1 = (-a+b+1) + 2·(n-b) + (B) |
| n ≥ b+1, a ≥ 2, A ≤ 0 | -a+b+B | -1 | S+1 = (-a+b+1) + (B) |
| n ≥ b+1, A ≥ 1, a ≥ 3 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| a = 1, A ≥ 1 | b-A+B+1 | 0 | S = (b) + (-A+B+1) |
| a = 1, A ≤ 0 | b+B-1 | -1 | S+1 = (b) + (B) |
| b ≥ n, A ≥ 1, a ≥ 3 | 2·n-a-b-A+B+2 | 0 | S = (-a+b+1) + 2·(n-b) + (-A+B+1) |
| b ≥ n, A ≥ 1, a ≤ 2 | 2·n+a-b-A+B-2 | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-2) |
| n ≥ b+1, a = 2, A ≥ 1 | a+b-A+B-2 | 0 | S = (-a+b+1) + (-A+B+1) + 2·(a-2) |

*Zones (0,2).*  n03 = n,  u12 = 0,  n14 = pos(min(b,n))+pos(n+1-(n+1-A)+1)-2·(pos(min(min(b,n),n+1)-(max(1,n+1-A))+1)),  w24 = n,  u02 = [a≥2],  n04 = n,  n13 = [a≥1]+pos(a-1-(2)+1)+pos(B+1)-2·(pos(min([a≥1],B+1))+pos(min(a-1,B+1)-(max(2,1))+1)),  w23 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≤ 0 | b+A-B | 0 | S = (b) + (A-B) |
| n ≥ b+A+1, a ≥ B+3 | -a+b+A+B+2 | 1 | S−1 = (-a+b+1) + 2·(B) + (A-B) |
| b+A ≥ n, a ≥ B+3 | 2·n-a-b-A+B+2 | 0 | S = (-a+b+1) + 2·(n-b) + (-A+B+1) |
| b+A ≥ n, a ≤ 1 | 2·n-b-A-B+1 | 2 | S−2 = (a-b) + (A-B) + 2·(n-A-1) + (-a+1) |
| n ≥ b+A+1, a ≥ 2, B ≥ a-2 | a+b+A-B-2 | 1 | S−1 = (-a+b+1) + (A-B) + 2·(a-2) |
| n ≥ b+A+1, a = 1 | b+A-B+1 | 1 | S−1 = (b) + (A-B) |
| b+A ≥ n, a ≥ 2, B ≥ a-2 | 2·n+a-b-A-B-2 | 0 | S = (a-b) + (A-B) + 2·(n-A-1) |

*Zones (1,0).*  n03 = [a≥1]+pos(a-1-(2)+1)+pos(n-(n+2-A)+1)-2·(pos(min([a≥1],n)-(max(1,n+2-A))+1)+pos(min(a-1,n)-(max(2,n+2-A))+1)),  u12 = pos(max(b,1)),  n14 = n+pos(n+[A≥1]-(n+1)+1)-2·(pos(min(n,n+[A≥1])-(max(1,n+1))+1)),  w24 = 0,  u02 = 1+[a≥2],  n04 = [b≥1]+pos(n-1+[B≥1]-(n)+1)+pos(B-1)-2·(pos(min([b≥1],n-1+[B≥1])-(max(1,n))+1)+pos(min([b≥1],B-1))),  n13 = n,  w23 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≤ 0, A ≥ n+1 | A-B | 1 | S−1 = (n-B) + (-n+A-1) |
| a ≤ 0, B ≥ 1 | A-B | 0 | S = (A-B) |
| a ≤ 0, A ≤ 0 | 0 | 0 | S = 0 |
| a ≤ 0, A ≥ n | A-B | 0 | S = (A-B) |
| a ≥ 2, A ≥ n+1, n ≥ 3 | -a+b+A-B | 0 | S = (-a+b+1) + (n-B) + (-n+A-1) |
| a ≥ 2, A ≥ n+1, n ≤ 2 | -2·n-a+b+A-B+4 | 0 | S = (-a+b+1) + (n-B) + (-n+A-1) + 2·(-n+2) |
| a ≥ 2, n ≥ a+A-1, B ≥ 2 | a+b+A-B-2 | 1 | S−1 = (-a+b+1) + (A-B) + 2·(a-2) |
| a ≥ 2, A ≤ 0, n ≥ 3 | a+b-4 | -1 | S+1 = (-a+b+1) + 2·(a-2) |
| a ≥ 2, A ≤ 0, n ≤ 2 | -2·n+a+b | -1 | S+1 = (-a+b+1) + 2·(a-2) + 2·(-n+2) |
| a ≥ 2, A ≥ n, B ≤ 1 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| n ≥ A+1, a+A ≥ n+2, B ≥ 2 | 2·n-a+b-A-B+2 | 3 | S−3 = (-a+b+1) + (A-B) + 2·(n-A-1) |
| n ≥ A+1, a+A ≥ n+2, B ≤ 1 | 2·n-a+b-A+B-2 | 2 | S−2 = 3·(-a+b+1) + 2·(n-b-1) + (-A+B+1) + 2·(n-A-1) + 2·(-n+a+A-2) |
| a ≥ 1, A ≥ n+1, b ≤ 0 | A-B-1 | 0 | S = (n-B) + (-n+A-1) |
| a ≥ 1, A ≤ 0, b ≤ 0 | 1 | 1 | S−1 = 0 |
| a ≤ 0, A ≥ 1, B ≤ 0 | A | 1 | S−1 = (A-1) |
| a ≥ 2, n ≥ A+1, B ≥ 1, n ≤ 2 | -2·n+a+b+A+B-2 | -1 | S+1 = (-a+b+1) + (A-B) + 2·(a-2) + 2·(B-1) + 2·(-n+2) |
| a ≥ 2, A ≥ 1, B ≤ 0, n ≥ 3 | a+b+A-4 | 0 | S = (-a+b+1) + 2·(a-2) + (A-1) |
| a ≥ 2, A ≥ 1, B ≤ 0, n ≤ 2 | -2·n+a+b+A | 0 | S = (-a+b+1) + 2·(a-2) + (A-1) + 2·(-n+2) |
| a ≥ 2, n ≥ A, n ≤ 2, B ≥ 2 | -a+b-A-B+6 | 1 | S−1 = (-a+b+1) + (n-B) + (n-A) + 2·(-n+2) |
| a ≥ 2, n = A, n ≥ 3 | 2·n-a+b-A-B+2 | 1 | S−1 = (-a+b+1) + (n-B) + (n-A) |
| a ≥ 1, n ≥ A+1, b ≤ 0, B ≥ 1 | A-B+1 | 1 | S−1 = (A-B) |
| a ≥ 1, A ≥ 1, b ≤ 0, B ≤ 0 | A+1 | 2 | S−2 = (A-1) |
| a ≥ 1, n = A, b ≤ 0 | 2·n-A-B+1 | 1 | S−1 = (n-B) + (n-A) |
| a ≤ 1, n ≥ A+1, b ≥ 1, B ≥ 2 | b+A-B+1 | 2 | S−2 = (A-B) + (b-1) |
| a ≤ 1, A ≥ n+1, b ≥ 1, n ≥ 3 | b+A-B-1 | 1 | S−1 = (n-B) + (-n+A-1) + (b-1) |
| a ≤ 1, A ≥ n+1, b ≥ 1, n ≤ 2 | -2·n+b+A-B+3 | 1 | S−1 = (n-B) + (-n+A-1) + (b-1) + 2·(-n+2) |
| a ≤ 1, A ≤ 0, b ≥ 1, n ≥ 3 | b-1 | 0 | S = (b-1) |
| a ≤ 1, A ≤ 0, b ≥ 1, n ≤ 2 | -2·n+b+3 | 0 | S = (b-1) + 2·(-n+2) |
| a ≤ 1, A ≥ n, b ≥ 1, B ≤ 1 | b-A+B+1 | 1 | S−1 = (-A+B+1) + (b-1) |
| a ≥ 2, n ≥ a+A-1, B = 1, n ≥ 3 | a+b+A+B-6 | -1 | S+1 = (-a+b+1) + (A-B) + 2·(a-2) + 2·(B-1) |
| a ≤ 1, n ≥ A+1, b ≥ 1, B ≥ 1, n ≤ 2 | -2·n+b+A+B+1 | 0 | S = (A-B) + (b-1) + 2·(B-1) + 2·(-n+2) |
| a ≤ 1, A ≥ 1, b ≥ 1, B ≤ 0, n ≥ 3 | b+A-1 | 1 | S−1 = (A-1) + (b-1) |
| a ≤ 1, A ≥ 1, b ≥ 1, B ≤ 0, n ≤ 2 | -2·n+b+A+3 | 1 | S−1 = (A-1) + (b-1) + 2·(-n+2) |
| a ≤ 1, b ≥ 1, B = 1, n ≥ 3 | b+A+B-3 | 0 | S = (A-B) + (b-1) + 2·(B-1) |
| a ≤ 1, n ≥ A, b ≥ 1, n ≤ 2, B ≥ 2 | b-A-B+5 | 2 | S−2 = (n-B) + (n-A) + (b-1) + 2·(-n+2) |
| a ≤ 1, n = A, b ≥ 1, n ≥ 3 | 2·n+b-A-B+1 | 2 | S−2 = (n-B) + (n-A) + (b-1) |

*Zones (1,1).*  n03 = [a≥1]+pos(a-1-(2)+1)+n-2·(pos(min([a≥1],n))+pos(min(a-1,n)-(max(2,1))+1)),  u12 = pos(max(b,1)),  n14 = n+pos(n+1-(n+1)+1)-2·(pos(min(n,n+1)-(max(1,n+1))+1)),  w24 = pos(B),  u02 = 1+[a≥2],  n04 = [b≥1]+n-2·(pos(min([b≥1],n))),  n13 = n+[A≥1]-2·(pos(min(n,[A≥1]))),  w23 = pos(max(A,1))

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2, A ≥ 1 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| a ≥ 2, A ≤ 0 | -a+b+B | -1 | S+1 = (-a+b+1) + (B) |
| a ≤ 0, A ≥ 1 | -A+B+2 | 1 | S−1 = (-A+B+1) |
| a ≤ 0, A ≤ 0 | B | 0 | S = (B) |
| a ≥ 1, b ≤ 0, A ≥ 1 | -A+B+1 | 0 | S = (-A+B+1) |
| a ≥ 1, b ≤ 0, A ≤ 0 | B-1 | -1 | S+1 = (B) |
| a ≤ 1, b ≥ 1, A ≥ 1 | b-A+B+1 | 1 | S−1 = (-A+B+1) + (b-1) |
| a ≤ 1, b ≥ 1, A ≤ 0 | b+B-1 | 0 | S = (B) + (b-1) |

*Zones (1,2).*  n03 = [a≥1]+pos(a-1-(2)+1)+n-2·(pos(min([a≥1],n))+pos(min(a-1,n)-(max(2,1))+1)),  u12 = pos(max(b,1)),  n14 = n+pos(n+1-(n+1-A)+1)-2·(pos(min(n,n+1)-(max(1,n+1-A))+1)),  w24 = n,  u02 = 1+[a≥2],  n04 = [b≥1]+n-2·(pos(min([b≥1],n))),  n13 = n+pos(B+1)-2·(pos(min(n,B+1))),  w23 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2, n ≥ B+2 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| a ≥ 2, B ≥ n-1 | 2·n-a+b-A-B | 1 | S−1 = (-a+b+1) + (A-B) + 2·(n-A-1) |
| a ≤ 0, n ≥ B+2 | -A+B+2 | 1 | S−1 = (-A+B+1) |
| a ≤ 0, B ≥ n-1 | 2·n-A-B | 2 | S−2 = (A-B) + 2·(n-A-1) |
| a ≥ 1, b ≤ 0, n ≥ B+2 | -A+B+1 | 0 | S = (-A+B+1) |
| a ≥ 1, b ≤ 0, B ≥ n-1 | 2·n-A-B-1 | 1 | S−1 = (A-B) + 2·(n-A-1) |
| a ≤ 1, b ≥ 1, n ≥ B+2 | b-A+B+1 | 1 | S−1 = (-A+B+1) + (b-1) |
| a ≤ 1, b ≥ 1, B ≥ n-1 | 2·n+b-A-B-1 | 2 | S−2 = (A-B) + 2·(n-A-1) + (b-1) |

*Zones (2,0).*  n03 = pos(n-1+[a≥n-1])+pos(n-(n+2-A)+1)-2·(pos(min(n-1+[a≥n-1],n)-(max(1,n+2-A))+1)),  u12 = n,  n14 = n+pos(n+[A≥1]-(n+1)+1)-2·(pos(min(n,n+[A≥1])-(max(1,n+1))+1)),  w24 = 0,  u02 = pos(min(a+2,n)),  n04 = pos(b+1)+pos(n-1+[B≥1]-(n)+1)+pos(B-1)-2·(pos(min(b+1,n-1+[B≥1])-(max(1,n))+1)+pos(min(b+1,B-1))),  n13 = n,  w23 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| A ≥ n+1, n ≥ b+3 | -a+b+A-B | 0 | S = (-a+b+1) + (n-B) + (-n+A-1) |
| A ≥ n+1, b ≥ B-1 | -3·n+b+A+B+1 | 1 | S−1 = 2·(-A+B+1) + 3·(-n+A-1) + (b-B+1) |
| A ≤ 0, n ≥ b+3 | 2·n-a-b-4 | 1 | S−1 = (-a+b+1) + 2·(n-b-3) |
| A ≤ 0, b ≥ n-1 | n-b-1 | 0 | S = (a-b) + (n-a-1) |
| A ≥ 2, n ≥ b+3, b ≥ B-1 | 2·n-a-b-A+B-2 | 2 | S−2 = (-a+b+1) + (-A+B+1) + 2·(n-b-3) |
| n ≥ a+2, A ≥ n+1, b ≥ n-2 | -2·n-a+3·b+A-B+4 | 1 | S−1 = (n-B) + (n-a-2) + (-n+A-1) + 3·(-n+b+2) |
| n ≥ a+2, A ≤ 0, b ≥ n-2 | -a+b | 0 | S = (n-a-2) + (-n+b+2) |
| A ≥ 1, B ≤ 0, n ≥ b+3 | 2·n-a-b+A-4 | 2 | S−2 = (-a+b+1) + (A-1) + 2·(n-b-3) |
| A ≥ 1, B ≤ 0, b ≥ n-1 | n-b-A+1 | 1 | S−1 = (a-b) + (n-a-1) + (-A+B+1) + (-B) |
| A ≤ 1, B ≥ 1, n ≥ b+3 | 2·n-a-b+A+B-6 | 1 | S−1 = (-a+b+1) + (A-B) + 2·(B-1) + 2·(n-b-3) |
| a ≥ n-1, A ≥ n+1, B ≥ b+2 | -3·n+3·b+A-B+5 | 0 | S = 3·(-a+b+1) + (n-B) + 3·(-n+a+1) + (-n+A-1) |
| a ≥ n-1, A ≤ 0, n ≥ b+2 | -n+b+3 | 1 | S−1 = (-a+b+1) + (-n+a+1) |
| a ≥ n-1, n ≥ A, B ≥ b+2 | -n+3·b-A-B+7 | 1 | S−1 = 3·(-a+b+1) + (n-B) + 3·(-n+a+1) + (n-A) |
| n ≥ A, n ≥ b+3, B ≥ b+2 | 2·n-a+b-A-B+2 | 1 | S−1 = (-a+b+1) + (n-B) + (n-A) |
| n ≥ a+2, A ≥ 2, b ≥ n-2, b ≥ B-1 | -a+b-A+B+2 | 1 | S−1 = (-A+B+1) + (n-a-2) + (-n+b+2) |
| n ≥ a+2, A ≥ 1, B ≤ 0, b ≥ n-2 | -a+b+A | 1 | S−1 = (n-a-2) + (A-1) + (-n+b+2) |
| n ≥ a+2, A ≤ 1, B ≥ 1, b ≥ n-2 | -a+b+A+B-2 | 0 | S = (A-B) + (n-a-2) + 2·(B-1) + (-n+b+2) |
| n ≥ a+2, n ≥ A, b ≥ n-2, B ≥ b+2 | -a+3·b-A-B+6 | 2 | S−2 = (n-B) + (n-a-2) + (n-A) + 3·(-n+b+2) |
| a ≥ n-1, A ≥ 1, B ≤ 0, n ≥ b+2 | -n+b-A+5 | 2 | S−2 = (-a+b+1) + (-A+B+1) + (-n+a+1) + (-B) |
| a ≥ n-1, n ≥ A, B ≥ 1, b ≥ B-1 | -n+b-A+B+3 | 0 | S = (-a+b+1) + (-A+B+1) + (-n+a+1) |

*Zones (2,1).*  n03 = pos(n-1+[a≥n-1])+n-2·(pos(min(n-1+[a≥n-1],n))),  u12 = n,  n14 = n+pos(n+1-(n+1)+1)-2·(pos(min(n,n+1)-(max(1,n+1))+1)),  w24 = pos(B),  u02 = pos(min(a+2,n)),  n04 = pos(b+1)+n-2·(pos(min(b+1,n))),  n13 = n+[A≥1]-2·(pos(min(n,[A≥1]))),  w23 = pos(max(A,1))

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, A ≥ 1 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| n ≥ a+2, A ≤ 0 | -a+b+B | -1 | S+1 = (-a+b+1) + (B) |
| a ≥ n-1, A ≥ 1 | -n+b-A+B+3 | 0 | S = (-a+b+1) + (-A+B+1) + (-n+a+1) |
| a ≥ n-1, A ≤ 0 | -n+b+B+1 | -1 | S+1 = (-a+b+1) + (B) + (-n+a+1) |

*Zones (2,2).*  n03 = pos(n-1+[a≥n-1])+n-2·(pos(min(n-1+[a≥n-1],n))),  u12 = n,  n14 = n+pos(n+1-(n+1-A)+1)-2·(pos(min(n,n+1)-(max(1,n+1-A))+1)),  w24 = n,  u02 = pos(min(a+2,n)),  n04 = pos(b+1)+n-2·(pos(min(b+1,n))),  n13 = n+pos(B+1)-2·(pos(min(n,B+1))),  w23 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, n ≥ B+2 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| n ≥ a+2, B ≥ n-1 | 2·n-a+b-A-B | 1 | S−1 = (-a+b+1) + (A-B) + 2·(n-A-1) |
| a ≥ n-1, n ≥ B+2 | -n+b-A+B+3 | 0 | S = (-a+b+1) + (-A+B+1) + (-n+a+1) |
| a ≥ n-1, B ≥ n-1 | n+b-A-B+1 | 1 | S−1 = (-a+b+1) + (A-B) + 2·(n-A-1) + (-n+a+1) |

**Pair (1,3).**  odd = K+1 + S,   S = u02 + w04 + n13 + n24 − u01 − w03 − n14 − n23   (to show: S ≥ -2)

*Zones (0,0).*  u02 = [b≥2],  w04 = pos(n-1+[B≥1]-(n)+1)+pos(B-1),  n13 = [b≥1]+pos(b-1-(2)+1),  n24 = 0,  u01 = [a≥n+1],  w03 = pos(n-(n+2-A)+1),  n14 = pos(n+[A≥1]-(n+1)+1),  n23 = pos(min(a,n))

| case | S | ≥ | certificate |
|---|---|---|---|
| B ≥ 1, a ≥ n+1 | -n+b-A+B-1 | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-n+a-1) |
| B ≥ 1, b ≤ 0 | -a-A+B | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-b) |
| a ≥ n+1, A ≤ 0 | -n+b-1 | -1 | S+1 = (-a+b+1) + (-n+a-1) |
| b ≤ 0, A ≤ 0 | -a | -1 | S+1 = (-a+b+1) + (-b) |
| b ≥ 2, B ≥ 1, n ≥ a | -a+b-A+B | -2 | S+2 = (-a+b+1) + (-A+B+1) |
| b ≥ 2, n ≥ a, A ≤ 0 | -a+b | -1 | S+1 = (-a+b+1) |
| b = 1, B ≥ 1 | -a-A+B+1 | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-b+1) |
| b = 1, A ≤ 0 | -a+1 | -1 | S+1 = (-a+b+1) + (-b+1) |
| B ≤ 0, a ≥ n+1, A ≥ 1 | -n+b-A-1 | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-B) + (-n+a-1) |
| B ≤ 0, b ≤ 0, A ≥ 1 | -a-A | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-B) + (-b) |
| b ≥ 2, B ≤ 0, n ≥ a, A ≥ 1 | -a+b-A | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-B) |
| b = 1, B ≤ 0, A ≥ 1 | -a-A+1 | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-b+1) + (-B) |

*Zones (0,1).*  u02 = [b≥2],  w04 = n,  n13 = [b≥1]+pos(b-1-(2)+1)+[A≥1]-2·(pos(min([b≥1],[A≥1]))+pos(min(b-1,[A≥1])-(max(2,1))+1)),  n24 = pos(B),  u01 = [a≥n+1],  w03 = n,  n14 = pos(n+1-(n+1)+1),  n23 = pos(min(a,n))+pos(max(A,1))-2·(pos(min(min(a,n),max(A,1))))

| case | S | ≥ | certificate |
|---|---|---|---|
| b ≥ 3, A ≥ a | a+b-A+B-2 | 3 | S−3 = (a-b) + (-A+B+1) + 2·(b-3) |
| A ≤ 0, a ≥ n+1 | -n+b+B-1 | -1 | S+1 = (-a+b+1) + (B) + (-n+a-1) |
| b ≤ 0, A ≥ 1 | a-A+B | -1 | S+1 = (b) + (a-b) + (-A+B+1) |
| b ≤ 0, A ≤ 0 | a+B-2 | -2 | S+2 = (b) + (a-b) + (B) |
| b ≥ 3, a ≥ n+1, A ≥ n | n+b-A+B-3 | 2 | S−2 = (n-b) + (-A+B+1) + 2·(b-3) |
| b = 2, A ≥ a | a-b-A+B+2 | 1 | S−1 = (a-b) + (-A+B+1) |
| b ≥ 2, A ≤ 0, n ≥ a | -a+b+B | -1 | S+1 = (-a+b+1) + (B) |
| b ≥ 1, A ≤ 0, a ≤ 1 | a+B-1 | 0 | S = (a-b) + (B) + (b-1) |
| b ≤ 1, A ≥ 1, a ≥ A+1 | -a+A+B-1 | -2 | S+2 = (-a+b+1) + (B) + (-b+1) + (A-1) |
| b = 1, A ≥ a | a-A+B-1 | -1 | S+1 = (a-b) + (-A+B+1) + (b-1) |
| b ≤ 1, A ≤ 0, a ≥ 2 | -a+B+1 | -1 | S+1 = (-a+b+1) + (B) + (-b+1) |
| b ≤ 2, a ≥ n+1, A ≥ n | n-b-A+B+1 | 0 | S = (n-b) + (-A+B+1) |
| A ≥ 1, b ≥ 3, a ≥ n+1, n ≥ A+1 | -n+b+A+B-3 | -2 | S+2 = (-a+b+1) + (B) + (A-1) + (-n+a-1) |
| A ≥ 1, b ≥ 3, n ≥ a, a ≥ A+1 | -a+b+A+B-2 | -2 | S+2 = (-a+b+1) + (B) + (A-1) |
| A ≥ 1, b ≤ 2, a ≥ n+1, n ≥ A+1 | -n-b+A+B+1 | -2 | S+2 = (-a+b+1) + (B) + (A-1) + 2·(-b+2) + (-n+a-1) |
| b = 2, A ≥ 1, n ≥ a, a ≥ A+1 | -a-b+A+B+2 | -2 | S+2 = (-a+b+1) + (B) + (A-1) + 2·(-b+2) |

*Zones (0,2).*  u02 = [b≥2],  w04 = n,  n13 = [b≥1]+pos(b-1-(2)+1)+pos(B+1)-2·(pos(min([b≥1],B+1))+pos(min(b-1,B+1)-(max(2,1))+1)),  n24 = n,  u01 = [a≥n+1],  w03 = n,  n14 = pos(n+1-(n+1-A)+1),  n23 = pos(min(a,n))+n-2·(pos(min(min(a,n),n)))

| case | S | ≥ | certificate |
|---|---|---|---|
| b ≤ 0 | a-A+B | -1 | S+1 = (b) + (a-b) + (-A+B+1) |
| b ≥ B+3, a ≥ n+1 | n+b-A-B-3 | 2 | S−2 = (n-b) + (-A+B+1) + 2·(b-B-3) |
| b ≥ B+3, n ≥ a | a+b-A-B-2 | 3 | S−3 = (a-b) + (-A+B+1) + 2·(b-B-3) |
| b = 1 | a-A+B-1 | -1 | S+1 = (a-b) + (-A+B+1) + (b-1) |
| B ≥ b-2, a ≥ n+1 | n-b-A+B+1 | 0 | S = (n-b) + (-A+B+1) |
| b ≥ 2, B ≥ b-2, n ≥ a | a-b-A+B+2 | 1 | S−1 = (a-b) + (-A+B+1) |

*Zones (1,0).*  u02 = 1+[a≥2],  w04 = pos(n-1+[B≥1]-(n)+1)+pos(B-1),  n13 = n,  n24 = pos(b),  u01 = 1,  w03 = pos(n-(n+2-A)+1),  n14 = [a≥1]+pos(a-1-(2)+1)+pos(n+[A≥1]-(n+1)+1)-2·(pos(min([a≥1],n+[A≥1])-(max(1,n+1))+1)+pos(min(a-1,n+[A≥1])-(max(2,n+1))+1)),  n23 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2, B ≥ 1 | -a+b-A+B+2 | 0 | S = (-a+b+1) + (-A+B+1) |
| a ≥ 2, A ≤ 0 | -a+b+2 | 1 | S−1 = (-a+b+1) |
| B ≥ 1, a ≤ 0 | b-A+B | -1 | S+1 = (b) + (-A+B+1) |
| A ≤ 0, a ≤ 0 | b | 0 | S = (b) |
| a ≥ 2, B ≤ 0, A ≥ 1 | -a+b-A+2 | 0 | S = (-a+b+1) + (-A+B+1) + (-B) |
| a = 1, B ≥ 1 | b-A+B-1 | -2 | S+2 = (b) + (-A+B+1) |
| a = 1, A ≤ 0 | b-1 | -1 | S+1 = (b) |
| B ≤ 0, A ≥ 1, a ≤ 0 | b-A | -1 | S+1 = (b) + (-A+B+1) + (-B) |
| a = 1, B ≤ 0, A ≥ 1 | b-A-1 | -2 | S+2 = (b) + (-A+B+1) + (-B) |

*Zones (1,1).*  u02 = 1+[a≥2],  w04 = n,  n13 = n+[A≥1]-2·(pos(min(n,[A≥1]))),  n24 = pos(b)+pos(B)-2·(pos(min(b,B))),  u01 = 1,  w03 = n,  n14 = [a≥1]+pos(a-1-(2)+1)+pos(n+1-(n+1)+1)-2·(pos(min([a≥1],n+1)-(max(1,n+1))+1)+pos(min(a-1,n+1)-(max(2,n+1))+1)),  n23 = n+pos(max(A,1))-2·(pos(min(n,max(A,1))))

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2, A ≤ 0 | -a+b-B+2 | 1 | S−1 = (-a+b+1) + (A-B) + (-A) |
| a ≥ 2, A ≥ n | 2·n-a-b-A+B | 0 | S = (-a+b+1) + 2·(n-b-1) + (-A+B+1) |
| A ≤ 0, a ≤ 0 | -b+B | 0 | S = (a-b) + (B) + (-a) |
| a ≤ 0, A ≥ n | 2·n-b-A+B-2 | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-2) + (-a) |
| a ≥ 2, A ≥ 1, b ≥ B+1 | -a+b+A-B | -1 | S+1 = (-a+b+1) + (A-B) |
| a ≥ 2, B ≥ b, n ≥ A+1 | -a-b+A+B | -1 | S+1 = (-a+b+1) + (A-B) + 2·(-b+B) |
| A ≥ 1, a ≤ 0, n ≥ A+1 | -b+A+B-2 | -1 | S+1 = (a-b) + (B) + (A-1) + (-a) |
| a ≤ 1, A ≥ 1, b ≥ B+1 | b+A-B-3 | -1 | S+1 = (A-1) + (b-B-1) |
| a = 1, A ≥ n | 2·n-b-A+B-3 | -1 | S+1 = (n-b-1) + (-A+B+1) + (n-2) |
| a ≤ 1, A ≤ 0, b ≥ B+1 | b-B-1 | 0 | S = (b-B-1) |
| A ≤ 0, B ≥ b, a ≥ 1 | -b+B-1 | -1 | S+1 = (-b+B) |
| a = 1, A ≥ 1, B ≥ b, n ≥ A+1 | -b+A+B-3 | -2 | S+2 = (A-1) + (-b+B) |

*Zones (1,2).*  u02 = 1+[a≥2],  w04 = n,  n13 = n+pos(B+1)-2·(pos(min(n,B+1))),  n24 = pos(b)+n-2·(pos(min(b,n))),  u01 = 1,  w03 = n,  n14 = [a≥1]+pos(a-1-(2)+1)+pos(n+1-(n+1-A)+1)-2·(pos(min([a≥1],n+1)-(max(1,n+1-A))+1)+pos(min(a-1,n+1)-(max(2,n+1-A))+1)),  n23 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ B+2, a+A ≥ n+1 | a-b+A-B-2 | -2 | S+2 = (a-b) + (A-B) |
| n ≥ B+2, a ≤ 0 | 2·n-b-A-B-2 | 1 | S−1 = (a-b) + (n-A-1) + (n-B-2) + (-a) |
| a ≥ 2, B ≥ n-1 | -2·n+a-b+A+B | -2 | S+2 = (a-b) + (A-B) + 2·(-n+B+1) |
| a ≥ 2, n ≥ a+A | 2·n-a-b-A-B | 0 | S = (a-b) + (A-B) + 2·(n-a-A) |
| B ≥ n-1, a ≤ 0 | -b-A+B | 0 | S = (a-b) + (n-A-1) + (-n+B+1) + (-a) |
| a ≥ 2, n ≥ B+2, A ≥ n-1 | a-b+A-B-2 | -1 | S+1 = (a-b) + (n-B-2) + (-n+A+1) |
| a = 1, n ≥ A+2 | 2·n-b-A-B-3 | 0 | S = (a-b) + (A-B) + (-a+1) + 2·(n-A-2) |
| a = 1, B ≥ n-1 | -2·n-b+A+B+1 | -2 | S+2 = (a-b) + (A-B) + (-a+1) + 2·(-n+B+1) |
| a = 1, n ≥ B+2, A ≥ n-1 | -b+A-B-1 | -1 | S+1 = (a-b) + (-a+1) + (n-B-2) + (-n+A+1) |

*Zones (2,0).*  u02 = pos(min(a+2,n)),  w04 = pos(n-1+[B≥1]-(n)+1)+pos(B-1),  n13 = n,  n24 = n,  u01 = pos(b+1),  w03 = pos(n-(n+2-A)+1),  n14 = pos(n-1+[a≥n-1])+pos(n+[A≥1]-(n+1)+1)-2·(pos(min(n-1+[a≥n-1],n+[A≥1])-(max(1,n+1))+1)),  n23 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, B ≥ 1 | a-b-A+B+2 | 1 | S−1 = (a-b) + (-A+B+1) |
| n ≥ a+2, A ≤ 0 | a-b+2 | 2 | S−2 = (a-b) |
| a ≥ n-1, B ≥ 1 | n-b-A+B-1 | -1 | S+1 = (a-b) + (n-a-1) + (-A+B+1) |
| a ≥ n-1, A ≤ 0 | n-b-1 | 0 | S = (a-b) + (n-a-1) |
| n ≥ a+2, B ≤ 0, A ≥ 1 | a-b-A+2 | 1 | S−1 = (a-b) + (-A+B+1) + (-B) |
| a ≥ n-1, B ≤ 0, A ≥ 1 | n-b-A-1 | -1 | S+1 = (a-b) + (n-a-1) + (-A+B+1) + (-B) |

*Zones (2,1).*  u02 = pos(min(a+2,n)),  w04 = n,  n13 = n+[A≥1]-2·(pos(min(n,[A≥1]))),  n24 = n+pos(B)-2·(pos(min(n,B))),  u01 = pos(b+1),  w03 = n,  n14 = pos(n-1+[a≥n-1])+pos(n+1-(n+1)+1)-2·(pos(min(n-1+[a≥n-1],n+1)-(max(1,n+1))+1)),  n23 = n+pos(max(A,1))-2·(pos(min(n,max(A,1))))

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, A ≤ 0 | a-b-B+2 | 2 | S−2 = (a-b) + (A-B) + (-A) |
| n ≥ a+2, A ≥ n | 2·n+a-b-A-B | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-B-1) |
| a ≥ n-1, A ≤ 0 | n-b-B-1 | 0 | S = (a-b) + (n-a-1) + (A-B) + (-A) |
| a ≥ n-1, A ≥ n | 3·n-b-A-B-3 | -1 | S+1 = (a-b) + (n-a-1) + (-A+B+1) + 2·(n-B-1) |
| n ≥ a+2, A ≥ 1, n ≥ A+1 | a-b+A-B | 0 | S = (a-b) + (A-B) |
| a ≥ n-1, A ≥ 1, n ≥ A+1 | n-b+A-B-3 | -2 | S+2 = (a-b) + (n-a-1) + (A-B) |

*Zones (2,2).*  u02 = pos(min(a+2,n)),  w04 = n,  n13 = n+pos(B+1)-2·(pos(min(n,B+1))),  n24 = 0,  u01 = pos(b+1),  w03 = n,  n14 = pos(n-1+[a≥n-1])+pos(n+1-(n+1-A)+1)-2·(pos(min(n-1+[a≥n-1],n+1)-(max(1,n+1-A))+1)),  n23 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, B ≥ n-1 | -2·n+a-b+A+B | -2 | S+2 = (a-b) + (A-B) + 2·(-n+B+1) |
| n ≥ a+2, A ≤ 0 | a-b-A-B | 0 | S = (a-b) + (A-B) + 2·(-A) |
| a ≥ n-1, n ≥ B+2 | n-b+A-B-3 | -2 | S+2 = (a-b) + (n-a-1) + (A-B) |
| a ≥ n-1, B ≥ n-1 | -n-b+A+B-1 | -2 | S+2 = (a-b) + (n-a-1) + (A-B) + 2·(-n+B+1) |
| n ≥ a+2, n ≥ B+2, A ≥ 1 | a-b+A-B-2 | -2 | S+2 = (a-b) + (A-B) |

**Pair (0,4).**  odd = K+1 + S,   S = n04 + n12 + u13 − w01 − n02 − n03 − u14   (to show: S ≥ -2)

*Zones (0,T).*  n04 = pos(n-1+[A≥2]-(n)+1),  n12 = pos(n-(n+3-A)+1),  u13 = [a≥1]+pos(a-1-(2)+1),  w01 = [B≥1],  n02 = [a≥2]+[A≥1]-2·(pos(min([a≥2],[A≥1]))),  n03 = pos(n-(n+2-B)+1),  u14 = pos(min(b,n))

| case | S | ≥ | certificate |
|---|---|---|---|
| A ≥ 2, a ≥ 2 | a-b+A-B-2 | -2 | S+2 = (a-b) + (A-B) |
| A ≥ 2, a ≤ 0 | -b+A-B-2 | -2 | S+2 = (a-b) + (A-B) + (-a) |
| a ≥ 2, A ≤ 0 | a-b-2 | -2 | S+2 = (a-b) |
| a ≤ 0, A ≤ 0 | -b | 0 | S = (a-b) + (-a) |
| A ≥ 2, a = 1 | -b+A-B-1 | -2 | S+2 = (a-b) + (A-B) + (-a+1) |
| a ≥ 2, B ≤ 0, A ≥ 1 | a-b-1 | -1 | S+1 = (a-b) |
| a = 1, A ≤ 0 | -b+1 | 0 | S = (a-b) + (-a+1) |
| A ≤ 1, a ≥ 2, B ≥ 1 | a-b-B-1 | -2 | S+2 = (a-b) + (A-B) + (-A+1) |
| A ≤ 1, a ≤ 0, B ≥ 1 | -b-B-1 | -2 | S+2 = (a-b) + (A-B) + (-A+1) + (-a) |
| a ≤ 0, B ≤ 0, A ≥ 1 | -b-1 | -1 | S+1 = (a-b) + (-a) |
| a = 1, B ≤ 0, A ≥ 1 | -b | -1 | S+1 = (a-b) + (-a+1) |
| A ≤ 1, a = 1, B ≥ 1 | -b-B | -2 | S+2 = (a-b) + (A-B) + (-A+1) + (-a+1) |

*Zones (1,T).*  n04 = [b≥1]+pos(n-1+[A≥2]-(n)+1)-2·(pos(min([b≥1],n-1+[A≥2])-(max(1,n))+1)),  n12 = pos(max(b,1))+pos(n-(n+3-A)+1)-2·(pos(min(max(b,1),n)-(max(1,n+3-A))+1)),  u13 = n,  w01 = [B≥1],  n02 = 1+[a≥2]+[A≥1]-2·(pos(min(1+[a≥2],[A≥1]))),  n03 = [a≥1]+pos(a-1-(2)+1)+pos(n-(n+2-B)+1)-2·(pos(min([a≥1],n)-(max(1,n+2-B))+1)+pos(min(a-1,n)-(max(2,n+2-B))+1)),  u14 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| A ≥ n+2, a ≤ 0 | A-B-2 | -1 | S+1 = (n-B+1) + (-n+A-2) |
| A ≤ 0, a ≤ 0 | 0 | 0 | S = 0 |
| n ≥ 3, A ≥ n+2, a ≥ 2 | a-b+A-B-2 | -1 | S+1 = (a-b) + (n-B+1) + (-n+A-2) |
| n ≥ 3, a ≥ 2, A ≤ 0 | -a+b | -1 | S+1 = (-a+b+1) |
| A ≥ 2, n ≥ A, a ≤ 0 | A-B | 0 | S = (A-B) |
| b+A ≥ n+2, a ≥ 2, n ≥ a+B-1 | 2·n-a-b-A-B+4 | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-a-B+1) |
| A ≤ 1, B ≥ 1, a ≤ 0 | -B+1 | 0 | S = (A-B) + (-A+1) |
| n = A-1, a ≤ 0 | 2·n-A-B+2 | 0 | S = (n-B+1) + (n-A+1) |
| n ≤ 2, A ≥ n+2, a ≥ 2 | 2·n+a-b+A-B-6 | 0 | S = (n-b-1) + (n-B+1) + (n-2) + (-n+A-2) + (a-2) |
| n ≤ 2, a ≥ 2, A ≤ 0 | 2·n-a+b-4 | -1 | S+1 = (-a+b+1) + 2·(n-2) |
| B ≤ 0, A ≥ 1, a ≤ 0 | 1 | 1 | S−1 = 0 |
| b ≤ 0, A ≥ n+2, a ≥ 1 | A-B-1 | 0 | S = (n-B+1) + (-n+A-2) |
| b ≤ 0, A ≤ 0, a ≥ 1 | -1 | -1 | S+1 = 0 |
| n ≥ 3, b+A ≥ n+2, a ≤ 1, n ≥ B | -b-A+B+3 | 1 | S−1 = (a-b) + (-A+B+1) + (-a+1) |
| n ≥ 3, b+A ≥ n+2, n ≥ B, a+B ≥ n+2 | a-b-A+B | -1 | S+1 = (a-b) + (-A+B+1) |
| n ≥ 3, n ≥ b+A-1, a ≥ 2, B ≥ n | -2·n+a+b+A+B-4 | -1 | S+1 = (-a+b+1) + (A-B) + 2·(a-2) + 2·(-n+B) |
| n ≥ 3, n ≥ A-1, a ≥ 2, B ≥ n+1 | 2·n+a-b-A-B+2 | 0 | S = (a-b) + (n-B+1) + (n-A+1) |
| n ≥ 3, B ≤ 0, a ≥ 2, A ≥ 1 | -a+b+1 | 0 | S = (-a+b+1) |
| A ≥ 2, n ≤ 2, a ≥ 2, n ≥ B+1 | 2·n-a+b+A-B-4 | 0 | S = (-a+b+1) + (n-2) + (A-2) + (n-B-1) |
| b ≥ 1, n ≥ 3, A ≥ n+2, a ≤ 1 | -b+A-B+1 | 1 | S−1 = (a-b) + (n-B+1) + (-n+A-2) + (-a+1) |
| b ≥ 1, n ≥ 3, n ≥ b+A-1, a+B ≥ n+2 | -2·n+a+b+A+B-4 | -1 | S+1 = (-a+b+1) + (A-B) + 2·(-n+a+B-2) |
| b ≥ 1, n ≥ 3, a ≤ 1, A ≤ 0 | b-1 | 0 | S = (b-1) |
| b ≥ 1, n ≤ 2, A ≥ n+2, a ≤ 1 | 2·n-b+A-B-3 | 1 | S−1 = (n-b-1) + (n-B+1) + (n-2) + (-n+A-2) |
| b ≥ 1, n ≤ 2, a ≤ 1, A ≤ 0 | 2·n+b-5 | 0 | S = 2·(n-2) + (b-1) |
| A ≤ 1, n ≥ 3, B ≥ 1, a ≥ 2 | -a+b-B+1 | -1 | S+1 = (-a+b+1) + (A-B) + (-A+1) |
| A ≤ 1, n ≤ 2, B ≥ 1, a ≥ 2 | 2·n-a+b-B-3 | -1 | S+1 = (-a+b+1) + (A-B) + 2·(n-2) + (-A+1) |
| n ≤ 2, b+A ≥ n+2, a ≥ 2, n ≥ B | 2·n+a-b-A+B-4 | 0 | S = (n-b-1) + (-A+B+1) + (n-2) + (a-2) |
| n ≤ 2, b+A ≥ n+2, a ≤ 1, n ≥ B | 2·n-b-A+B-1 | 1 | S−1 = (n-b-1) + (-A+B+1) + (n-2) |
| n ≤ 2, n ≥ b+A-1, a ≥ 2, B ≥ n | a+b+A+B-8 | -1 | S+1 = (-a+b+1) + (A-B) + 2·(n-2) + 2·(a-2) + 2·(-n+B) |
| n ≤ 2, n ≥ A-1, a ≥ 2, B ≥ n+1 | 4·n+a-b-A-B-2 | 1 | S−1 = (n-b-1) + (n-B+1) + (n-2) + (n-A+1) + (a-2) |
| n ≤ 2, B ≤ 0, a ≥ 2, A ≥ 1 | 2·n-a+b-3 | 0 | S = (-a+b+1) + 2·(n-2) |
| b ≤ 0, A ≥ 2, a ≥ 1, n ≥ B+1 | A-B-1 | -1 | S+1 = (A-B) |
| b ≤ 0, A ≥ n+1, a ≥ 1, n ≥ B | -A+B+1 | 0 | S = (-A+B+1) |
| b ≤ 0, A ≤ 1, B ≥ 1, a ≥ 1 | -B | -1 | S+1 = (A-B) + (-A+1) |
| b ≤ 0, n ≥ A-1, a ≥ 1, B ≥ n+1 | 2·n-A-B+3 | 1 | S−1 = (n-B+1) + (n-A+1) |
| b ≤ 0, n ≥ A, a ≥ 1, B ≥ n | -2·n+A+B-1 | -1 | S+1 = (A-B) + 2·(-n+B) |
| b ≤ 0, B ≤ 0, A ≥ 1, a ≥ 1 | 0 | 0 | S = 0 |
| n ≥ 3, b+A ≥ n+2, a ≥ 2, n = B | a-b-A+B | -1 | S+1 = (a-b) + (-A+B+1) |
| A ≥ 2, n ≥ 3, n ≥ b+A-1, a ≥ 2, n ≥ a+B-1 | -a+b+A-B | -1 | S+1 = (-a+b+1) + (A-B) |
| b ≥ 1, n ≥ 3, n ≥ b+A-1, a ≤ 1, B ≥ n | -2·n+b+A+B-1 | 0 | S = (A-B) + (b-1) + 2·(-n+B) |
| b ≥ 1, n ≥ 3, n ≥ A-1, a ≤ 1, B ≥ n+1 | 2·n-b-A-B+5 | 2 | S−2 = (a-b) + (n-B+1) + (n-A+1) + (-a+1) |
| b ≥ 1, n ≥ 3, B ≤ 0, a ≤ 1, A ≥ 1 | b | 1 | S−1 = (b-1) |
| b ≥ 1, A ≥ 2, n ≥ 3, a ≤ 1, n ≥ B+1 | b+A-B-1 | 0 | S = (A-B) + (b-1) |
| b ≥ 1, A ≥ 2, n ≤ 2, a ≤ 1, n ≥ B+1 | 2·n+b+A-B-5 | 1 | S−1 = (n-2) + (b-1) + (A-2) + (n-B-1) |
| b ≥ 1, A ≤ 1, n ≥ 3, B ≥ 1, a ≤ 1 | b-B | 0 | S = (A-B) + (b-1) + (-A+1) |
| b ≥ 1, A ≤ 1, n ≤ 2, B ≥ 1, a ≤ 1 | 2·n+b-B-4 | 0 | S = (A-B) + 2·(n-2) + (b-1) + (-A+1) |
| b ≥ 1, n ≤ 2, n ≥ b+A-1, a ≤ 1, B ≥ n | b+A+B-5 | 0 | S = (A-B) + 2·(n-2) + (b-1) + 2·(-n+B) |
| b ≥ 1, n ≤ 2, n ≥ A-1, a ≤ 1, B ≥ n+1 | 4·n-b-A-B+1 | 2 | S−2 = (n-b-1) + (n-B+1) + (n-2) + (n-A+1) |
| b ≥ 1, n ≤ 2, B ≤ 0, a ≤ 1, A ≥ 1 | 2·n+b-4 | 1 | S−1 = 2·(n-2) + (b-1) |

*Zones (2,T).*  n04 = pos(b+1)+pos(n-1+[A≥2]-(n)+1)-2·(pos(min(b+1,n-1+[A≥2])-(max(1,n))+1)),  n12 = n+pos(n-(n+3-A)+1)-2·(pos(n-(max(1,n+3-A))+1)),  u13 = n,  w01 = [B≥1],  n02 = pos(min(a+2,n))+[A≥1]-2·(pos(min(min(a+2,n),[A≥1]))),  n03 = pos(n-1+[a≥n-1])+pos(n-(n+2-B)+1)-2·(pos(min(n-1+[a≥n-1],n)-(max(1,n+2-B))+1)),  u14 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ b+3, A ≥ n+2 | -a+b+A-B-2 | -2 | S+2 = (-a+b+1) + (n-B+1) + (-n+A-2) |
| n ≥ b+3, A ≤ 0 | -a+b | -1 | S+1 = (-a+b+1) |
| A ≥ n+2, a ≥ n-1 | n-b+A-B-3 | -1 | S+1 = (a-b) + (n-a-1) + (n-B+1) + (-n+A-2) |
| b ≥ n-1, A ≤ 0 | -n+b+1 | 0 | S = (-n+b+1) |
| n ≥ b+3, n ≥ A-1, B ≥ n+1 | 2·n-a+b-A-B+2 | -1 | S+1 = (-a+b+1) + (n-B+1) + (n-A+1) |
| n ≥ b+3, B ≤ 0, A ≥ 1 | -a+b+1 | 0 | S = (-a+b+1) |
| n ≥ b+3, n ≥ B, B ≥ 2 | -a+b-A+B | -2 | S+2 = (-a+b+1) + (-A+B+1) |
| A ≥ 2, n ≥ b+3, B ≤ 1 | -a+b-A-B+4 | 0 | S = (-a+b+1) + (-A+B+1) + 2·(-B+1) |
| A ≥ 2, a ≥ n-1, n ≥ B | n-b-A+B-1 | -1 | S+1 = (a-b) + (n-a-1) + (-A+B+1) |
| n ≥ b+2, a ≥ n-1, A ≤ 0 | n-b-3 | -1 | S+1 = (n-b-2) |
| A ≤ 1, n ≥ b+3, B ≥ 1 | -a+b-B+1 | -1 | S+1 = (-a+b+1) + (A-B) + (-A+1) |
| A ≤ 1, b ≥ n-1, B ≥ 1 | -n+b+B | 0 | S = (-n+b+1) + (B-1) |
| n ≥ A-1, a ≥ n-1, B ≥ n+1 | 3·n-b-A-B+1 | 0 | S = (a-b) + (n-a-1) + (n-B+1) + (n-A+1) |
| b ≥ n-1, B ≤ 0, A ≥ 1 | -n+b+2 | 1 | S−1 = (-n+b+1) |
| b ≥ n-2, A ≥ n+2, n ≥ a+2 | 2·n-a-b+A-B-6 | -1 | S+1 = (a-b) + (n-B+1) + (-n+A-2) + 2·(n-a-2) |
| b ≥ n-2, n ≥ a+2, A ≤ 0 | 2·n-a-b-4 | 0 | S = (a-b) + 2·(n-a-2) |
| A ≥ 2, b ≥ n-2, n ≥ a+2, B ≤ 1 | 2·n-a-b-A-B | 1 | S−1 = (a-b) + (-A+B+1) + 2·(n-a-2) + 2·(-B+1) |
| n ≥ b+2, B ≤ 0, a ≥ n-1, A ≥ 1 | n-b-2 | 0 | S = (n-b-2) |
| A ≤ 1, n ≥ b+2, B ≥ 1, a ≥ n-1 | n-b+B-4 | -1 | S+1 = (n-b-2) + (B-1) |
| A ≤ 1, b ≥ n-2, B ≥ 1, n ≥ a+2 | 2·n-a-b-B-3 | 0 | S = (a-b) + (A-B) + (-A+1) + 2·(n-a-2) |
| b ≥ n-2, n ≥ a+2, n ≥ B, B ≥ 2 | 2·n-a-b-A+B-4 | -1 | S+1 = (a-b) + (-A+B+1) + 2·(n-a-2) |
| b ≥ n-2, n ≥ A-1, n ≥ a+2, B ≥ n+1 | 4·n-a-b-A-B-2 | 0 | S = (a-b) + (n-B+1) + (n-A+1) + 2·(n-a-2) |
| b ≥ n-2, B ≤ 0, n ≥ a+2, A ≥ 1 | 2·n-a-b-3 | 1 | S−1 = (a-b) + 2·(n-a-2) |

**Pair (1,4).**  odd = K + S,   S = n02 + w03 + u14 + u23 − n01 − w04 − w12 − u13 − u24   (to show: S ≥ -1)

*Zones (0,T).*  n02 = [b≥2]+[A≥1]-2·(pos(min([b≥2],[A≥1]))),  w03 = pos(n-(n+2-B)+1),  u14 = 0,  u23 = pos(min(a,n)),  n01 = [a≥n+1]+[B≥1]-2·(pos(min([a≥n+1],[B≥1]))),  w04 = pos(n-1+[A≥2]-(n)+1),  w12 = pos(n-(n+3-A)+1),  u13 = [b≥1]+pos(b-1-(2)+1),  u24 = 0

| case | S | ≥ | certificate |
|---|---|---|---|
| A ≥ 2, b ≤ 0 | a-A+B | -1 | S+1 = (b) + (a-b) + (-A+B+1) |
| a ≥ n+1, A ≥ 2 | n-b-A+B+1 | 0 | S = (n-b) + (-A+B+1) |
| A ≤ 0, a ≥ n+1 | n-b+1 | 1 | S−1 = (n-b) |
| A ≤ 0, b ≤ 0 | a | 0 | S = (b) + (a-b) |
| b ≥ 2, A ≤ 0, n ≥ a | a-b+2 | 2 | S−2 = (a-b) |
| b ≥ 2, n ≥ a, A ≥ 2 | a-b-A+B | -1 | S+1 = (a-b) + (-A+B+1) |
| A ≥ 1, B ≤ 0, a ≥ n+1 | n-b | 0 | S = (n-b) |
| A ≥ 1, B ≤ 0, b ≤ 0 | a+1 | 1 | S−1 = (b) + (a-b) |
| B ≥ 1, a ≥ n+1, A ≤ 1 | n-b+B | 1 | S−1 = (n-b) + (B-1) |
| B ≥ 1, A ≤ 1, b ≤ 0 | a+B-1 | 0 | S = (b) + (a-b) + (B-1) |
| b = 1, A ≥ 2 | a-A+B-1 | -1 | S+1 = (a-b) + (-A+B+1) + (b-1) |
| b = 1, A ≤ 0 | a-1 | 0 | S = (a-b) + (b-1) |
| b ≥ 2, A ≥ 1, B ≤ 0, n ≥ a | a-b+1 | 1 | S−1 = (a-b) |
| b ≥ 2, B ≥ 1, n ≥ a, A ≤ 1 | a-b+B-1 | 0 | S = (a-b) + (B-1) |
| b = 1, A ≥ 1, B ≤ 0 | a | 1 | S−1 = (a-b) + (b-1) |
| b = 1, B ≥ 1, A ≤ 1 | a+B-2 | 0 | S = (a-b) + (B-1) + (b-1) |

*Zones (1,T).*  n02 = 1+[a≥2]+[A≥1]-2·(pos(min(1+[a≥2],[A≥1]))),  w03 = pos(n-(n+2-B)+1),  u14 = [a≥1]+pos(a-1-(2)+1),  u23 = n,  n01 = 1+[B≥1]-2·(pos(min(1,[B≥1]))),  w04 = pos(n-1+[A≥2]-(n)+1),  w12 = pos(n-(n+3-A)+1),  u13 = n,  u24 = pos(b)

| case | S | ≥ | certificate |
|---|---|---|---|
| a ≥ 2, A ≥ 2 | a-b-A+B | -1 | S+1 = (a-b) + (-A+B+1) |
| a ≥ 2, A ≤ 0 | a-b | 0 | S = (a-b) |
| A ≤ 0, a ≤ 0 | -b | 0 | S = (a-b) + (-a) |
| a ≤ 0, A ≥ 2 | -b-A+B | -1 | S+1 = (a-b) + (-A+B+1) + (-a) |
| a ≥ 2, A ≥ 1, B ≤ 0 | a-b-1 | -1 | S+1 = (a-b) |
| a ≥ 2, B ≥ 1, A ≤ 1 | a-b+B-1 | 0 | S = (a-b) + (B-1) |
| A ≥ 1, B ≤ 0, a ≤ 0 | -b-1 | -1 | S+1 = (a-b) + (-a) |
| B ≥ 1, a ≤ 0, A ≤ 1 | -b+B-1 | 0 | S = (a-b) + (B-1) + (-a) |
| a = 1, A ≥ 2 | -b-A+B+1 | -1 | S+1 = (a-b) + (-A+B+1) + (-a+1) |
| a = 1, A ≤ 0 | -b+1 | 0 | S = (a-b) + (-a+1) |
| a = 1, A ≥ 1, B ≤ 0 | -b | -1 | S+1 = (a-b) + (-a+1) |
| a = 1, B ≥ 1, A ≤ 1 | -b+B | 0 | S = (a-b) + (-a+1) + (B-1) |

*Zones (2,T).*  n02 = pos(min(a+2,n))+[A≥1]-2·(pos(min(min(a+2,n),[A≥1]))),  w03 = pos(n-(n+2-B)+1),  u14 = pos(n-1+[a≥n-1]),  u23 = n,  n01 = pos(b+1)+[B≥1]-2·(pos(min(b+1,[B≥1]))),  w04 = pos(n-1+[A≥2]-(n)+1),  w12 = pos(n-(n+3-A)+1),  u13 = n,  u24 = n

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ a+2, A ≤ 0 | a-b | 0 | S = (a-b) |
| a ≥ n-1, A ≤ 0 | n-b-1 | 0 | S = (a-b) + (n-a-1) |
| n ≥ a+2, A ≥ 1, B ≤ 0 | a-b-1 | -1 | S+1 = (a-b) |
| n ≥ a+2, b ≥ 1, A ≥ 2 | a-b-A+B | -1 | S+1 = (a-b) + (-A+B+1) |
| n ≥ a+2, b ≤ 0, A ≥ 2 | a+b-A+B | -1 | S+1 = 2·(b) + (a-b) + (-A+B+1) |
| a ≥ n-1, A ≥ 1, B ≤ 0 | n-b-2 | -1 | S+1 = (a-b) + (n-a-1) |
| a ≥ n-1, b ≥ 1, A ≥ 2 | n-b-A+B-1 | -1 | S+1 = (a-b) + (n-a-1) + (-A+B+1) |
| a ≥ n-1, b ≤ 0, A ≥ 2 | n+b-A+B-1 | 0 | S = (b) + (-A+B+1) + (n-2) |
| n ≥ a+2, B ≥ 1, b ≥ 1, A ≤ 1 | a-b+B-1 | 0 | S = (a-b) + (B-1) |
| n ≥ a+2, B ≥ 1, b ≤ 0, A ≤ 1 | a+b+B-1 | 0 | S = 2·(b) + (a-b) + (B-1) |
| a ≥ n-1, B ≥ 1, b ≥ 1, A ≤ 1 | n-b+B-2 | 0 | S = (a-b) + (n-a-1) + (B-1) |
| a ≥ n-1, B ≥ 1, b ≤ 0, A ≤ 1 | n+b+B-2 | 1 | S−1 = (b) + (n-2) + (B-1) |

**Pair (2,4).**  odd = K+1 + S,   S = w01 + n03 + u13 + u24 − n02 − w04 − n12 − u34   (to show: S ≥ -2)

*Zones (0,T).*  w01 = [B≥1],  n03 = pos(n-(n+2-a)+1)+pos(n-(n+2-B)+1)-2·(pos(n-(max(n+2-a,n+2-B))+1)),  u13 = [b≥1]+pos(b-1-(2)+1),  u24 = 0,  n02 = [b≥2]+[A≥1]-2·(pos(min([b≥2],[A≥1]))),  w04 = pos(n-1+[A≥2]-(n)+1),  n12 = pos(n-(n+3-A)+1),  u34 = [a≥1]

| case | S | ≥ | certificate |
|---|---|---|---|
| b ≥ 2, A ≤ 0 | a+b-4 | 0 | S = (a-b) + 2·(b-2) |
| B ≥ a, b ≥ 2 | -a+b-A+B | -2 | S+2 = (-a+b+1) + (-A+B+1) |
| a ≤ 0, A ≥ 2 | -A+B | -1 | S+1 = (-A+B+1) |
| a ≤ 0, A ≤ 0 | 0 | 0 | S = 0 |
| a ≥ B+1, b ≥ 2, A ≥ 2 | a+b-A-B | 0 | S = (-a+b+1) + (-A+B+1) + 2·(a-B-1) |
| a ≥ B+1, b ≤ 1, A ≥ 2 | a-A-B+1 | 0 | S = (-a+b+1) + (-A+B+1) + 2·(a-B-1) + (-b+1) |
| B ≥ 1, b ≥ 2, A ≤ 1 | a+b-B-1 | 2 | S−2 = (a-b) + (A-B) + 2·(b-2) + (-A+1) |
| B ≥ 1, a ≤ 0, A ≤ 1 | B-1 | 0 | S = (B-1) |
| a ≥ 1, b ≤ 0, A ≥ 2 | -a-A+B | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-b) |
| a ≥ 1, b ≤ 0, A ≤ 0 | a-2 | -1 | S+1 = (a-1) |
| b = 1, A ≤ 0 | a-1 | 0 | S = (a-b) + (b-1) |
| B ≤ 0, b ≥ 2, A ≥ 1 | a+b-3 | 1 | S−1 = (a-b) + 2·(b-2) |
| B ≤ 0, a ≤ 0, A ≥ 1 | -1 | -1 | S+1 = 0 |
| B ≥ a, b ≥ 1, A ≤ 1 | -a+B | 0 | S = (-a+B) |
| B ≥ 1, a ≥ B+1, b ≤ 1, A ≤ 1 | a-B | 1 | S−1 = (a-B-1) |
| B ≥ 1, a ≥ 1, b ≤ 0, A ≤ 1 | -a+B-1 | -1 | S+1 = (-a+b+1) + (B-1) + (-b) |
| B ≤ 0, a ≥ 1, b ≤ 0, A ≥ 1 | a-3 | -2 | S+2 = (a-1) |
| B ≤ 0, b = 1, A ≥ 1 | a-2 | -1 | S+1 = (a-b) + (b-1) |
| B ≥ a, b = 1, A ≥ 2 | -a-A+B+1 | -2 | S+2 = (-a+b+1) + (-A+B+1) + (-b+1) |

*Zones (1,T).*  w01 = [B≥1],  n03 = n+pos(n-(n+2-B)+1)-2·(pos(n-(max(1,n+2-B))+1)),  u13 = n,  u24 = pos(b),  n02 = 1+[A≥1]-2·(pos(min(1,[A≥1]))),  w04 = pos(n-1+[A≥2]-(n)+1),  n12 = pos(n-(n+3-A)+1),  u34 = pos(a+1)

| case | S | ≥ | certificate |
|---|---|---|---|
| B ≥ n+1 | -a+b-A+B | -2 | S+2 = (-a+b+1) + (-A+B+1) |
| A ≤ 0 | 2·n-a+b-2 | 1 | S−1 = (-a+b+1) + 2·(n-2) |
| B ≥ 1, A ≤ 1 | 2·n-a+b-B+1 | 3 | S−3 = (-a+b+1) + (A-B) + 2·(n-2) + (-A+1) |
| B ≤ 0, A ≥ 1 | 2·n-a+b-1 | 2 | S−2 = (-a+b+1) + 2·(n-2) |
| n ≥ B, A ≥ 2 | 2·n-a+b-A-B+2 | 0 | S = (-a+b+1) + (-A+B+1) + 2·(n-B) |

*Zones (2,T).*  w01 = [B≥1],  n03 = n+pos(n-(n+2-B)+1)-2·(pos(n-(max(1,n+2-B))+1)),  u13 = n,  u24 = n,  n02 = 1+pos(min(b+2,n)-(3)+1)+pos(1+[b≥n-1]-(2)+1)+[A≥1]-2·(pos(min(1,[A≥1]))+pos(min(min(b+2,n),[A≥1])-(max(3,1))+1)+pos(min(1+[b≥n-1],[A≥1])-(max(2,1))+1)),  w04 = pos(n-1+[A≥2]-(n)+1),  n12 = pos(a)+pos(n-(n+3-A)+1)-2·(pos(min(a,n)-(max(1,n+3-A))+1)),  u34 = n+1

| case | S | ≥ | certificate |
|---|---|---|---|
| n ≥ b+2, A ≥ n+2 | a-b-A+B | -1 | S+1 = (a-b) + (-A+B+1) |
| n ≥ b+2, A ≤ 0 | 2·n-a-b-2 | 1 | S−1 = (n-a-1) + (n-b-2) |
| B ≥ n+1, n ≥ a+A-1 | -a-b-A+B | 0 | S = (a-b) + (A-B) + 2·(-n+B-1) + 2·(n-a-A+1) |
| b ≥ n-1, A ≥ n+2 | -n+a-A+B+1 | -1 | S+1 = (a-b) + (-A+B+1) + (-n+b+1) |
| b ≥ n-1, A ≤ 0 | n-a-1 | 0 | S = (n-a-1) |
| B ≥ 1, n ≥ b+2, A ≤ 1 | 2·n-a-b-B+1 | 3 | S−3 = (n-a-1) + (A-B) + (n-b-2) + (-A+1) |
| B ≥ 1, b ≥ n-1, A ≤ 1 | n-a-B+2 | 2 | S−2 = (n-a-1) + (A-B) + (-A+1) |
| B ≥ n+1, b ≥ n-1, n ≥ A-1 | -3·n+a+A+B-3 | -2 | S+2 = (a-b) + (A-B) + 2·(-n+B-1) + (-n+b+1) |
| b ≥ n-1, A ≥ 2, n ≥ a+A-1 | n-a-A-B+3 | 0 | S = (a-b) + (A-B) + (-n+b+1) + 2·(n-a-A+1) |
| B ≤ 0, n ≥ b+2, A ≥ 1 | 2·n-a-b-1 | 2 | S−2 = (n-a-1) + (n-b-2) |
| B ≤ 0, b ≥ n-1, A ≥ 1 | n-a | 1 | S−1 = (n-a-1) |
| n ≥ B, n ≥ b+2, a+A ≥ n+2 | a-b+A-B-2 | -2 | S+2 = (a-b) + (A-B) |
| n ≥ B, b ≥ n-1, a+A ≥ n+2 | -n+a+A-B-1 | -2 | S+2 = (a-b) + (A-B) + (-n+b+1) |
| B ≥ n+1, n ≥ b+2, n ≥ A-1, a+A ≥ n+2 | -2·n+a-b+A+B-4 | -2 | S+2 = (a-b) + (A-B) + 2·(-n+B-1) |
| n ≥ B, n ≥ b+2, A ≥ 2, n ≥ a+A-1 | 2·n-a-b-A-B+2 | 0 | S = (a-b) + (A-B) + 2·(n-a-A+1) |

<!--/ROWS-->

The cases of each zone pair are exhaustive and all stated bounds are >= the target of the pair, so Proposition B is
proved: 36 zone pairs, 441 cases. Verification: exact for all n: certificates and exhaustiveness (test_cert.py (1),
(1b)); exact at generation time (derive.py): "S = the linear form on the case"; numeric: the same for n = 2..40 on
all local coordinates (test_cert.py (2)) and on the words n = 2..10 (test_rows.py).

---------------------------------------------------------------------------------------------------------------------

## 6. Proof of the Theorem

Let 0 <= s < p <= L, s = jK+e, p = j'K+e'.
* j = j': letters of a piece (or of the tail) are distinct: odd = p - s.
* j' = j+1: Corollary A.
* j' >= j+2: length >= 2K - (K-1) = K+1 > k; odd = D_jj' + S >= K-1 = k by the Near-Simplex Lemma and Proposition B. QED
(For odd window lengths >= k, odd >= K follows by parity, see the parity remark.)

**Height function**: odd[s,p) = p - s (same piece); K - e + e' - 2 C_j(e,e') (adjacent; C_j = count from (O));
D_jj' + S (non-adjacent; S = linear form of a matching case). [test_theorem.py: equals odd[s,p) for all windows,
n = 2..10; path property; walk data (dn from the position table, steps +-1, H >= K at down-steps).]

---------------------------------------------------------------------------------------------------------------------

## 7. Range of n; tightness; kind of evidence

* **n >= 2 is used** as the fact (n-2) >= 0 in certificates and in the zone-column table (zone 1 has columns m = 0, 1
  with distinct special letters; for n = 1 the template does not apply, see the header of pfam4.py). No further small
  cases: n = 2, 3 are covered by the general argument and are part of every test.
* **Tightness.** The target (odd = k) is attained in 28 of the 36 zone pairs; not in (0,2):(0,1), (0,3):(0,2),
  (0,3):(1,2), (0,3):(2,0), (0,3):(2,2), (1,3):(0,2), (1,3):(2,0), (0,4):(1,T). Every stated case bound is attained on
  the words n <= 10.
* **Kind of evidence** (as in PROOF_family_second.md Section 7): Sections 1-4, 6 and rule (R) are hand arguments tested on the
  words; the State Table derivation is only sketched here (examples), but the table is tested for every prefix,
  n = 2..10; the case tables were found by derive.py; their bounds and exhaustiveness are re-verified exactly for all
  n by test_cert.py; "S = linear form on the case" is exact only inside derive.py, plus numeric checks.
* **Not addressed:** optimality of the length; n = 1.

---------------------------------------------------------------------------------------------------------------------

## 8. Lean plan

Same as PROOF_family_second.md Section 8, with: K = 6n+1, k = 6n, L = 26n+7, hypothesis `2 ≤ n`; word from the zone-column table
of Section 1 (coordinate number = base(type) + i - 1, types in the order 01 02 03 04 12 13 14 23 24 34, sizes n+1 for
14, 34 and n otherwise, as in pfam4_raw.py); occurrence lemmas from (O) (13_i occurs in P0..P3; 03_i in P0, P2, P3,
tail; 02_i in P0, P1, P2 and 02_1 also in the tail; 14_i in P0, P1, P3; 24_i in P1, P2, P3; 12_i in P0, P2, tail;
04_i in P0, P3 and 04_n also in the tail; 23_i in P1, P3; 01_i in P1 and 01_1 also in the tail; 34_i in P2 only);
`isPathWord_of_height` with H of Section 6. D depends on the pair (K-1, K, K+1). The State Table entries are unions
of intervals: define the term functions by rule (R) (min/max/truncated subtraction) and prove the 441 cases by
`omega`; certificates (multipliers 1..4, at most 5 conditions) are in cases.json. Closed forms for C_j are not
written here (count from (O)); they must be added and tested first (python twin in positions.py).
No parity case split is needed anywhere (parity remark).

---------------------------------------------------------------------------------------------------------------------

## 9. Tests (scripts and data files NOT included in this folder; python3; memory cap 1.5 GB in common.py; default n = 2..10, env NMAX)

| script | what it checks | result |
|---|---|---|
| test_states.py | Section 1: zone-column table (positions.column) = builder's word; (P); Section 3: State Table (states.py) = index sets of every prefix of every piece and the tail | OK, 1476 prefixes |
| test_slots.py | Section 1 (O): closed-form position table = word; Section 4: Slot Table (Phi_c in [p_c, q_c+1], disjoint), (A1), (A2), path property on all adjacent-piece windows incl. (P3, tail) | OK |
| test_simplex.py | Section 2: v_jK xor v_j'K = separating coordinates, sizes K-1 / K / K+1 as stated; d_H = D + S for all vertex pairs in different pieces | OK, 111078 vertex pairs |
| test_rows.py | Section 5 on the words: every term string = true symmetric-difference size; signs; D + signed sum = d_H; a case matches; every matching case formula = S; S >= lb >= target of the pair | OK, 61587 prefix pairs, 441 cases, every stated bound attained |
| test_cert.py (~3 min) | Section 5 for ALL n: (1) certificate identities in rational arithmetic, admissible facts, lb >= target; (1b) split trees complete, every leaf inside a case; (2) n = 2..40, all local coordinates: exhaustive, case formula = signed sum of term strings, >= lb | OK, 441 cases; 447 leaves; 3281967 points |
| test_theorem.py | Section 6: H = odd[s,p) for all windows; path property; walk data | OK, 142050 windows |
| test_mutation.py | 451 mutants of fam(2), fam(3) (all neighbour swaps, 150 random swaps per n, 9 named swaps): every mutant fails the equalities; every mutant that is not a path word (439) fails an inequality of the proof; 12 remain path words | OK |
| derive.py (~100 s) | generator of cases.json / fine.json; deterministic (re-run reproduces cases.json, md5 52ab4c8a...) | 36 zone pairs, 447 leaves, 441 cases |
| gen_tables.py | writes the State Table and the Section 5 tables into this file from states.py, terms.py, cases.json | - |
| `python3 pfam4.py 20` | the Theorem by the definition, n = 2..20 | 0 violations |

Data files: states.py, positions.py (zone-column table, position table, Slot Table), terms.py (rule (R)), lin.py
(linear forms, domain facts (E)), cases.json, fine.json, rows.py, common.py.
