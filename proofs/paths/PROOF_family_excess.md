# The first-excess family fam(t) is a spread-(6t-1) path of length 24t+2: hand proof for all t >= 3  (S179)

**Theorem.** Let t >= 3, K = 6t, k = K-1, d = 10t, and let T = fam(t) = P0 P1 P2 P3 tail (pfam2.py; Section 1), a word of
length L = 4K+2 = 24t+2 over d coordinates. Then T is the transition word of a spread-k path in Q_d: for all
0 <= s <= p <= L, with odd[s,p) = number of coordinates occurring an odd number of times in T[s..p-1] (= d_H(v_s, v_p)),

    p - s < k   implies   odd[s,p) = p - s,          p - s >= k   implies   odd[s,p) >= k.

(This is the window form of "d_H(v_s,v_p) < k implies d_H(v_s,v_p) = p-s", because odd[s,p) <= p-s always.)

Status: **complete, no gaps** (Section 7 says exactly where t >= 3 is used and what happens at t = 2).
Every numbered statement, every table entry and every case inequality is brute-force tested for t = 3..12 (Section 9
says by which script).

Proof idea. The five vertices v_0, v_K, v_2K, v_3K, v_4K form a regular simplex (pairwise distance K). A vertex inside
piece j is v_{jK} plus a prefix of P_j, so the distance between two vertices in different pieces is K plus a signed
count of the letters in the symmetric difference of two prefixes (Simplex Lemma). Each prefix is described by ten
index sets (State Table). For ADJACENT pieces everything follows from one injection (Slot Lemma). For NON-ADJACENT
pieces the claim is S >= -1 for an explicit signed sum S; it is checked zone pair by zone pair (36 rows, each a
two-line computation). No induction along the word and no Walk Lemma is needed.

---------------------------------------------------------------------------------------------------------------------

## 1. The word

Coordinates: (tau, i) with tau one of the ten 2-subsets of {0,..,4} (written 01, 02, .., 34; "the type") and
i = 1..t; we write tau_i. So d = 10t.

T = P0 P1 P2 P3 P4, where P0..P3 ("pieces") have length K = 6t and P4 = tail has length 2. Position jK+e is "offset e
of piece j". Each piece is cut into three **zones** z = 0, 1, 2 of length 2t (offsets [2tz, 2tz+2t)); inside a zone
the offsets are 2tz + 2n ("even column n") and 2tz + 2n+1 ("odd column n"), n = 0..t-1.

**Zone-column table** (this is the header table of pfam2.py, rewritten per zone; letter at even column n | at odd column n):

| piece | zone 0 | zone 1 | zone 2 |
|---|---|---|---|
| P0 | 13_{n+1} &#124; 14_1 (n=0), 03_n (n>=1) | 03_t (n=0), 14_{n+1} (n>=1) &#124; 12_{n+1} | 02_{n+1} &#124; 04_{n+1} |
| P1 | 13_{n+1} &#124; 23_{n+1} | 24_{n+1} &#124; 14_{n+1} | 02_{n+1} &#124; 01_{n+1} |
| P2 | 03_t (n=0), 13_{n+1} (n>=1) &#124; 13_1 (n=0), 34_n (n>=1) | 24_{n+1} &#124; 03_1 (n=0), 34_t (n=1), 03_n (n>=2) | 02_{n+1} &#124; 12_{n+1} |
| P3 | 03_t (n=0), 14_{n+1} (n>=1) &#124; 04_{n+1} | 24_{n+1} &#124; 14_1 (n=0), 13_{n+1} (n>=1) | 23_{n+1} &#124; 13_1 (n=0), 03_n (n>=1) |
| tail | 03_t, 12_t | | |

(The entry "34_t (n=1)" needs t >= 2; the definition makes sense for t >= 2.)

**(O) Position table**: offset of tau_i in each piece that contains it (read off the table above).

| piece | positions |
|---|---|
| P0 | 13_i: 2i-2;  14_1: 1;  14_i (i>=2): 2t+2i-2;  03_i (i<t): 2i+1;  03_t: 2t;  12_i: 2t+2i-1;  02_i: 4t+2i-2;  04_i: 4t+2i-1 |
| P1 | 13_i: 2i-2;  23_i: 2i-1;  24_i: 2t+2i-2;  14_i: 2t+2i-1;  02_i: 4t+2i-2;  01_i: 4t+2i-1 |
| P2 | 03_t: 0;  13_1: 1;  13_i (i>=2): 2i-2;  34_i (i<t): 2i+1;  34_t: 2t+3;  24_i: 2t+2i-2;  03_1: 2t+1;  03_i (2<=i<=t-1): 2t+2i+1;  02_i: 4t+2i-2;  12_i: 4t+2i-1 |
| P3 | 03_t: 0;  04_i: 2i-1;  14_i (i>=2): 2i-2;  14_1: 2t+1;  24_i: 2t+2i-2;  13_i (i>=2): 2t+2i-1;  13_1: 4t+1;  23_i: 4t+2i-2;  03_i (i<=t-1): 4t+2i+1 |
| tail | 03_t: 0;  12_t: 1 |

**(P) Incidence.** For j = 0..3: every tau_i with *exactly one of j, j+1 in tau* occurs exactly once in P_j, and
nothing else occurs in P_j. (Each row of (O) lists six types, each with every index i = 1..t once, 6t = K letters in
all; the six types are 13,14,03,12,02,04 / 13,23,24,14,02,01 / 03,13,34,24,02,12 / 03,04,14,24,13,23, which are the
types with exactly one of {0,1} / {1,2} / {2,3} / {3,4}.) In particular the letters of one piece are pairwise distinct.
[test_slots.py (1), test_states.py]

---------------------------------------------------------------------------------------------------------------------

## 2. The Simplex Lemma

A type tau **separates** j and j' if exactly one of j, j' lies in tau. Put sigma_{jj'}(tau) = -1 if tau separates
j, j' and +1 otherwise; sigma(c) = sigma(type of c) for a coordinate c.

Vertices: every position 0 <= p <= L is uniquely p = jK + e with (0 <= j <= 3 and 0 <= e < K) or (j = 4 and 0 <= e <= 2).
Write Pre_j(e) = set of the first e letters of P_j (a set of e distinct coordinates by (P); for j = 4 a subset of
{03_t, 12_t}).

**Simplex Lemma.** Let p = jK+e and p' = j'K+e' with j < j'. Then

    odd[p,p') = d_H(v_p, v_p') = K + S_{jj'}(e,e'),      S_{jj'}(e,e') := sum over c in Pre_j(e) symdiff Pre_j'(e') of sigma_{jj'}(c).

*Proof.* Identify vertices with sets of coordinates. By (P), v_{(j+1)K} = v_{jK} xor {tau_i : [j in tau] != [j+1 in tau]}
for j = 0..3, so by induction v_{jK} = v_0 xor {tau_i : [0 in tau] != [j in tau]} for j = 0..4, hence

    v_{jK} xor v_{j'K} = D_{jj'} := {tau_i : tau separates j, j'},      |D_{jj'}| = 6t = K   (j != j'),

(six types contain exactly one of two given elements). Now v_p = v_{jK} xor A, v_p' = v_{j'K} xor B with A = Pre_j(e),
B = Pre_j'(e'), so v_p xor v_p' = D xor X with X = A symdiff B and
|D xor X| = |D| + |X| - 2|D cap X| = K + #{c in X: c not in D} - #{c in X : c in D}. QED   [test_simplex.py]

**Per-type form.** For a type tau let I_j,tau(e) = {i : tau_i in Pre_j(e)} (empty if tau does not occur in P_j). Then

    (S)   S_{jj'}(e,e') = sum over the ten types tau of  sigma_{jj'}(tau) * n_tau,     n_tau = | I_j,tau(e) symdiff I_j',tau(e') |.

If tau occurs only in P_j we write u_tau = |I_j,tau(e)| for n_tau, if only in P_j' we write w_tau = |I_j',tau(e')|.

---------------------------------------------------------------------------------------------------------------------

## 3. The State Table

**Local coordinates.** For 0 <= e < K write e = 2tz + r with zone z in {0,1,2} and 0 <= r < 2t, and

    a = ceil(r/2),   b = floor(r/2).       (E1)   0 <= b <= a <= b+1,   b <= t-1,   a <= t;   b >= 1 implies a >= 1.

**(R0)** Pre_j(e) consists of all letters of the zones < z of P_j, the letters at even columns n of zone z with
n+1 <= a, and the letters at odd columns n of zone z with n+1 <= b. (2n < r iff n+1 <= a; 2n+1 < r iff n+1 <= b.)

Applying (R0) to the zone-column table gives the index sets I_j,tau(e). Notation: {1..q} is empty for q <= 0, {2..q} is
empty for q <= 1, [cond] = 1 if cond holds and 0 otherwise, "full" = {1..t}, "-" = empty, and

    M(b) = max(b-1, min(b,1))      (= 0, 1, 1, 2, 3, ... for b = 0, 1, 2, 3, 4, ...;     M(b) + [b>=2] = b,   M(b) <= t-1).

**State Table** (types not listed for a piece never occur in it):

| piece, zone | index sets I_tau after e = 2tz + r letters |
|---|---|
| P0, z=0 | 13: {1..a};  14: {1} if b>=1;  03: {1..b-1};  12, 02, 04: - |
| P0, z=1 | 13: full;  03: {1..t-1} + {t} if a>=1;  14: {1..max(a,1)};  12: {1..b};  02, 04: - |
| P0, z=2 | 13, 03, 14, 12: full;  02: {1..a};  04: {1..b} |
| P1, z=0 | 13: {1..a};  23: {1..b};  24, 14, 02, 01: - |
| P1, z=1 | 13, 23: full;  24: {1..a};  14: {1..b};  02, 01: - |
| P1, z=2 | 13, 23, 24, 14: full;  02: {1..a};  01: {1..b} |
| P2, z=0 | 03: {t} if a>=1;  13: {1..a} if b>=1, else -;  34: {1..b-1};  24, 02, 12: - |
| P2, z=1 | 03: {t} + {1..M(b)};  13: full;  34: {1..t-1} + {t} if b>=2;  24: {1..a};  02, 12: - |
| P2, z=2 | 03, 13, 34, 24: full;  02: {1..a};  12: {1..b} |
| P3, z=0 | 03: {t} if a>=1;  04: {1..b};  14: {2..a};  24, 13, 23: - |
| P3, z=1 | 03: {t};  04: full;  14: {2..t} + {1} if b>=1;  24: {1..a};  13: {2..b};  23: - |
| P3, z=2 | 03: {t} + {1..b-1};  04, 14, 24: full;  13: {2..t} + {1} if b>=1;  23: {1..a} |
| tail, e' = E in {0,1,2} | 03: {t} if E>=1;  12: {t} if E=2 |

Derivation of the less obvious entries. P0, z=0: odd column n carries 14_1 (n=0) and 03_n (n>=1), present iff n+1 <= b:
14_1 iff b >= 1, and 03_n for 1 <= n <= b-1. P0, z=1: zone 0 left 14: {1} and 03: {1..t-1}; even column n of zone 1
adds 03_t (n = 0, iff a >= 1) and 14_{n+1} for 1 <= n <= a-1, i.e. 14: {1} + {2..a} = {1..max(a,1)}.
P2, z=0: 13_1 sits at odd column 0 (iff b >= 1) and 13_{n+1} at even column n >= 1 (indices 2..a); for b = 0 we have
a <= 1 so nothing; for b >= 1 the set is {1..a}. P2, z=1: zone 0 left 34: {1..t-1}; odd column n of zone 1 adds 03_1
(n=0, iff b >= 1), 34_t (n=1, iff b >= 2), 03_n (2 <= n <= b-1): so 03: {t} + {1..M(b)}. P3, z=1: odd column n adds
14_1 (n = 0) and 13_{n+1} (1 <= n <= b-1), i.e. 13: {2..b}. P3, z=2: odd column n adds 13_1 (n=0) and 03_n
(1 <= n <= b-1). [test_states.py: the table is compared with the word for every prefix.]

---------------------------------------------------------------------------------------------------------------------

## 4. Adjacent pieces: the Slot Lemma

Let 0 <= j <= 3 and consider a window from offset e of P_j (0 <= e < K) to offset e' of P_{j+1} (0 <= e' < K; for
j = 3: 0 <= e' <= 2). Its length is w = K - e + e'. A coordinate c occurring in both pieces ("common letter") occurs
once in each (by (P)), at offsets p_c in P_j and q_c in P_{j+1}. So the coordinates occurring twice in the window are
the common letters with p_c >= e and q_c < e', all others occur at most once, and

    (A1)   odd[jK+e, (j+1)K+e') = w - 2 C_j(e,e'),        C_j(e,e') := #{common c : p_c >= e and q_c < e'}.

**Slot Lemma.** Suppose that to every common letter c of P_j, P_{j+1} an integer phi_c is assigned with
p_c <= phi_c <= q_c, such that the 2-element sets {phi_c, phi_c + 1} are pairwise disjoint. Then

    (A2)   C_j(e,e') <= max(0, floor((e' - e + 1)/2))     for all e, e'.

*Proof.* If c is counted in C_j(e,e') then e <= p_c <= phi_c and phi_c + 1 <= q_c + 1 <= e', so the slot
{phi_c, phi_c+1} lies in the integer interval [e, e'], which has max(0, e'-e+1) elements; the slots are disjoint. QED

**Slot Table.** The common types of P_j and P_{j+1} are those containing j+1 but neither j nor j+2 (two types), and
{j, j+2}. Positions from (O):

| pieces | common letter c: (p_c -> q_c), slot phi_c |
|---|---|
| P0, P1 | 13_i: (2i-2 -> 2i-2), phi = 2i-2;   14_1: (1 -> 2t+1), phi = 2t;   14_i (i>=2): (2t+2i-2 -> 2t+2i-1), phi = 2t+2i-2;   02_i: (4t+2i-2 -> 4t+2i-2), phi = 4t+2i-2 |
| P1, P2 | 13_1: (0 -> 1), phi = 0;   13_i (i>=2): (2i-2 -> 2i-2), phi = 2i-2;   24_i: (2t+2i-2 -> 2t+2i-2), phi = same;   02_i: (4t+2i-2 -> 4t+2i-2), phi = same |
| P2, P3 | 03_t: (0 -> 0), phi = 0;   13_1: (1 -> 4t+1), phi = 4t;   13_i (i>=2): (2i-2 -> 2t+2i-1), phi = 2i-2;   24_i: (2t+2i-2 -> 2t+2i-2), phi = same;   03_1: (2t+1 -> 4t+3), phi = 4t+2;   03_i (2<=i<=t-1): (2t+2i+1 -> 4t+2i+1), phi = 4t+2i |
| P3, tail | 03_t: (0 -> 0), phi = 0   (12_t does not occur in P3) |

In every row p_c <= phi_c <= q_c, all phi_c are even, and they are pairwise different: P0,P1: {0,..,2t-2}, 2t,
{2t+2,..,4t-2}, {4t,..,6t-2}; P1,P2: 0, {2,..,2t-2}, {2t,..,4t-2}, {4t,..,6t-2}; P2,P3: 0, 4t, {2,..,2t-2},
{2t,..,4t-2}, 4t+2, {4t+4,..,6t-2}. Distinct even numbers give disjoint slots. So (A2) holds for j = 0,1,2,3.
[test_slots.py (2), (3)]

**Corollary A (adjacent pieces).** For p = jK+e, p' = (j+1)K+e' as above the path property holds for the window [p,p').
*Proof.* If C_j(e,e') = 0 then odd = w by (A1), and both conditions hold. If C = C_j(e,e') >= 1 then by (A2)
e' - e + 1 >= 2C >= 2, so w = K + e' - e >= K+1 > k and odd = K + (e' - e) - 2C >= K - 1 = k. QED
(In particular two occurrences of a letter are at least K-1 apart.) [test_slots.py (4), (5)]

Explicit formulas for C_j (not needed for the proof; they make the height function explicit for Lean). Let
ev(x,y) = #{even p : x <= p < y} = max(0, ceil(y/2) - ceil(x/2)). From the Slot Table (letters grouped by row):

    (C01)  C_0(e,e') = ev(e, min(e',2t)) + [e <= 1 and e' >= 2t+2] + ev(max(e,2t+2), min(e'-1,4t)) + ev(max(e,4t), e')
    (C12)  C_1(e,e') = [e = 0 and e' >= 2] + ev(max(e,2), e')
    (C23)  C_2(e,e') = [e = 0 and e' >= 1] + [e <= 1 and e' >= 4t+2] + ev(max(e,2), min(2t, e'-2t-1)) + ev(max(e,2t), min(e',4t))
                       + [e <= 2t+1 and e' >= 4t+4] + ev(max(e,2t+5)+1, min(4t, e'-2t)+1)
    (C34)  C_3(e,e') = [e = 0 and e' >= 1]

[test_slots.py (3)]

---------------------------------------------------------------------------------------------------------------------

## 5. Non-adjacent pieces: S >= -1

**Proposition B.** For j' >= j+2 (pairs (0,2), (0,3), (1,3) and the tail pairs (0,4), (1,4), (2,4)), all 0 <= e < K and
all e' (0 <= e' < K, resp. 0 <= e' <= 2 for j' = 4):   S_{jj'}(e,e') >= -1.

The proof evaluates formula (S) on each pair of zones. Local coordinates: (z; a, b) for e in P_j and (z'; A, B) for
e' in P_j' (capital letters for the END prefix; for the tail, E = e'). Both satisfy (E1). We also use

    (E2)   abs(a - A) >= (b - B) - 1   and   abs(a - A) >= (B - b) - 1          (a - A >= b - (B+1),  A - a >= B - (b+1)).

The terms n_tau are computed from the State Table with the following rules (0 <= p, q <= t):

* (R1) |{1..p} symdiff {1..q}| = abs(p - q);  in particular = p against the empty set and t - p against the full set.
* (R2) |{1..p} symdiff ({t} + {1..q})| = 1 + abs(p - q) if p, q <= t-1;   = t - 1 - q if p = t;   two sets both
  containing t: |({t} + {1..p}) symdiff ({t} + {1..q})| = abs(p - q)  (p, q <= t-1).
* (R3) |{1..p} symdiff {2..q}| = N(p,q) := 1 + abs(p - q) if p >= 1,  q - 1 if p = 0   (q >= 1). With q = t:
  |{1..p} symdiff {2..t}| = t - p + 1 (p >= 1), t - 1 (p = 0), written t - p + [..]*(2[p>=1] - 1) below; and
  |{1..p} symdiff ({2..t} + {1})| = t - p.

In the tables: `pos(x)` = max(x,0), `abs` = absolute value, `M` as in Section 3, `N` as in (R3), `·` = product. For each
pair the first line gives formula (S) with its signs (types that occur in neither piece are omitted; + = type does not
separate j, j', − = it does). Each row lists the value of every term on that zone pair, then S simplified in each case
with a lower bound >= -1 and the reason. "E1"/"E2" refer to the inequalities above (E1: 0 <= a-b <= 1, 0 <= A-B <= 1,
a+b <= 2t-1, A+B <= 2t-1, and "b >= 1 implies a >= 1").

<!--ROWS-->
**Pair (0,2).**  S = n13 + n02 + u14 + w34 − n03 − n12 − u04 − w24

| zones (z,z') | terms | case: S = simplified formula ≥ bound  [reason] |
|---|---|---|
| (0,0) | n13 = abs(a-A·[B≥1]), n02 = 0, u14 = [b≥1], w34 = pos(B-1), n03 = pos(b-1)+[A≥1], n12 = 0, u04 = 0, w24 = 0 | b≥1, B≥1: S = abs(a-A)+B-b ≥ -1  [E2]<br>b=0, B≥1: S = A-a+B-2 ≥ -1  [a ≤ 1 ≤ A, B ≥ 1]<br>b≥1, B=0: S = a-b+2-[A≥1] ≥ 1  [a ≥ b]<br>b=0, B=0: S = a-[A≥1] ≥ -1  [a ≥ 0] |
| (0,1) | n13 = t-a, n02 = 0, u14 = [b≥1], w34 = t-1+[B≥2], n03 = 1+abs(pos(b-1)-M(B)), n12 = 0, u04 = 0, w24 = A | b≥1, B≥2: S = 2·t-a-A-abs(b-B) ≥ 0  [b ≥ B: a+A+b-B ≤ a+b+1 ≤ 2t; b < B: a+A+B-b ≤ 1+A+B ≤ 2t]<br>b≥1, B=1: S = 2·t-1-a-A-abs(b-2) ≥ 0  [A ≤ 2; b = 1: a ≤ 2, S ≥ 2t-6 (t ≥ 3 USED); b ≥ 2: a+b-2 ≤ 2t-3]<br>b≥1, B=0: S = 2·t-a-b-A ≥ 0  [a+b ≤ 2t-1, A ≤ 1]<br>b=0, B≥2: S = 2·t-a-A-B ≥ 0  [a ≤ 1, A+B ≤ 2t-1]<br>b=0, B=1: S = 2·t-3-a-A ≥ 0  [a ≤ 1, A ≤ 2: S ≥ 2t-6 (t ≥ 3 USED)]<br>b=0, B=0: S = 2·t-2-a-A ≥ 2  [a, A ≤ 1, t ≥ 3] |
| (0,2) | n13 = t-a, n02 = A, u14 = [b≥1], w34 = t, n03 = t-pos(b-1), n12 = B, u04 = 0, w24 = t | b≥1: S = (A-B)-(a-b) ≥ -1  [E1]<br>b=0: S = (A-B)-a ≥ -1  [a ≤ 1] |
| (1,0) | n13 = t-A·[B≥1], n02 = 0, u14 = max(a,1), w34 = pos(B-1), n03 = t-1+[[a≥1]≠[A≥1]], n12 = b, u04 = 0, w24 = 0 | B≥1, a≥1: S = (a-b)-(A-B) ≥ -1  [E1]<br>B≥1, a=0: S = -(A-B) ≥ -1  [E1]<br>B=0: S = 1+max(a,1)-b-[[a≥1]≠[A≥1]] ≥ 0  [max(a,1) ≥ b] |
| (1,1) | n13 = 0, n02 = 0, u14 = max(a,1), w34 = t-1+[B≥2], n03 = t-1-M(B)+[a=0], n12 = b, u04 = 0, w24 = A | always: S = (a-b)-(A-B) ≥ -1  [E1; uses M(B)+[B≥2] = B, max(a,1)-[a=0] = a] |
| (1,2) | n13 = 0, n02 = A, u14 = max(a,1), w34 = t, n03 = [a=0], n12 = abs(b-B), u04 = 0, w24 = t | always: S = a+A-abs(b-B) ≥ 0  [abs(b-B) ≤ max(b,B) ≤ max(a,A)] |
| (2,0) | n13 = t-A·[B≥1], n02 = a, u14 = t, w34 = pos(B-1), n03 = t-[A≥1], n12 = t, u04 = b, w24 = 0 | B≥1: S = (a-b)-(A-B) ≥ -1  [E1]<br>B=0: S = (a-b)+[A≥1] ≥ 0  [E1] |
| (2,1) | n13 = 0, n02 = a, u14 = t, w34 = t-1+[B≥2], n03 = t-1-M(B), n12 = t, u04 = b, w24 = A | always: S = (a-b)-(A-B) ≥ -1  [E1; M(B)+[B≥2] = B] |
| (2,2) | n13 = 0, n02 = abs(a-A), u14 = t, w34 = t, n03 = 0, n12 = t-B, u04 = b, w24 = t | always: S = abs(a-A)+B-b ≥ -1  [E2] |

**Pair (0,3).**  S = n03 + n14 + u12 + w24 − n13 − n04 − u02 − w23

| zones (z,z') | terms | case: S = simplified formula ≥ bound  [reason] |
|---|---|---|
| (0,0) | n03 = pos(b-1)+[A≥1], n14 = [b≥1]+pos(A-1), u12 = 0, w24 = 0, n13 = a, n04 = B, u02 = 0, w23 = 0 | always: S = (A-B)-(a-b) ≥ -1  [E1; pos(b-1)+[b≥1] = b] |
| (0,1) | n03 = pos(b-1)+1, n14 = t-1+[[b≥1]≠[B≥1]], u12 = 0, w24 = A, n13 = N(a,max(B,1)), n04 = t, u02 = 0, w23 = 0 | B=0: S = A-(a-b) ≥ -1  [E1]<br>B≥1, a=0: S = A-B+2 ≥ 2  [E1]<br>B≥1, a≥1, b=0: S = A-B+1 ≥ 1  [a = 1]<br>B≥1, b≥1: S = b-2+A-abs(a-B) ≥ -1  [a ≥ B: S = (b-a)+A+B-2; a < B: S = a+b+(A-B)-2 ≥ 0] |
| (0,2) | n03 = 1+abs(pos(b-1)-pos(B-1)), n14 = t-[b≥1], u12 = 0, w24 = t, n13 = t-a+[B=0]·(2·[a≥1]-1), n04 = t, u02 = 0, w23 = A | B≥1, b≥1: S = abs(b-B)+a-A ≥ -1  [abs(b-B) ≥ B-b, a ≥ b, A ≤ B+1]<br>B≥1, b=0: S = B-A+a ≥ -1  [E1]<br>B=0, b≥1: S = a+b-2-A ≥ -1  [a, b ≥ 1, A ≤ 1]<br>B=0, b=0: S = 2-a-A ≥ 0  [a, A ≤ 1] |
| (1,0) | n03 = t-1+[[a≥1]≠[A≥1]], n14 = 1+abs(max(a,1)-max(A,1)), u12 = b, w24 = 0, n13 = t, n04 = B, u02 = 0, w23 = 0 | a≥1, A≥1: S = abs(a-A)+b-B ≥ -1  [E2]<br>a=0, A≥1: S = A-B ≥ 0  [E1]<br>a≥1, A=0: S = a+b ≥ 1<br>a=0, A=0: S = 0 ≥ 0 |
| (1,1) | n03 = t-1+[a=0], n14 = t-max(a,1)+[B=0], u12 = b, w24 = A, n13 = t+1-max(B,1), n04 = t, u02 = 0, w23 = 0 | B≥1: S = (b-a)+A+B-2 ≥ -1  [A ≥ B ≥ 1]<br>B=0: S = (b-a)+A ≥ -1  [E1] |
| (1,2) | n03 = t-1-pos(B-1)+[a=0], n14 = t-max(a,1), u12 = b, w24 = t, n13 = [B=0], n04 = t, u02 = 0, w23 = A | B≥1: S = 2·t-(a-b)-A-B ≥ 0  [A+B ≤ 2t-1]<br>B=0: S = 2·t-2-(a-b)-A ≥ 2  [A ≤ 1, t ≥ 3] |
| (2,0) | n03 = t-[A≥1], n14 = t+1-max(A,1), u12 = t, w24 = 0, n13 = t, n04 = abs(b-B), u02 = a, w23 = 0 | always: S = 2·t-a-A-abs(b-B) ≥ 0  [b ≥ B: a+A+b-B ≤ a+b+1 ≤ 2t; b < B: a+A+B-b ≤ 1+A+B ≤ 2t] |
| (2,1) | n03 = t-1, n14 = [B=0], u12 = t, w24 = A, n13 = t+1-max(B,1), n04 = t-b, u02 = a, w23 = 0 | B≥1: S = (b-a)+A+B-2 ≥ -1  [A ≥ B ≥ 1]<br>B=0: S = (b-a)+A ≥ -1  [E1] |
| (2,2) | n03 = t-1-pos(B-1), n14 = 0, u12 = t, w24 = t, n13 = [B=0], n04 = t-b, u02 = a, w23 = A | B≥1: S = 2·t-(a-b)-A-B ≥ 0  [A+B ≤ 2t-1]<br>B=0: S = 2·t-2-(a-b)-A ≥ 2  [A ≤ 1, t ≥ 3] |

**Pair (1,3).**  S = n13 + n24 + u02 + w04 − n14 − n23 − u01 − w03

| zones (z,z') | terms | case: S = simplified formula ≥ bound  [reason] |
|---|---|---|
| (0,0) | n13 = a, n24 = 0, u02 = 0, w04 = B, n14 = pos(A-1), n23 = b, u01 = 0, w03 = [A≥1] | always: S = (a-b)-(A-B) ≥ -1  [E1; pos(A-1)+[A≥1] = A] |
| (0,1) | n13 = N(a,max(B,1)), n24 = A, u02 = 0, w04 = t, n14 = t-1+[B≥1], n23 = b, u01 = 0, w03 = 1 | B=0: S = (a-b)+A ≥ 0  [E1]<br>B≥1, a=0: S = A+B-2 ≥ 0  [A ≥ B ≥ 1]<br>B≥1, a≥1: S = abs(a-B)+A-b ≥ 0  [abs(a-B) ≥ a-B: S ≥ (a-b)+(A-B)] |
| (0,2) | n13 = t-a+[B=0]·(2·[a≥1]-1), n24 = t, u02 = 0, w04 = t, n14 = t, n23 = abs(b-A), u01 = 0, w03 = 1+pos(B-1) | B≥1: S = 2·t-a-B-abs(b-A) ≥ 0  [b ≥ A: a+B+b-A ≤ a+b ≤ 2t-1; b < A: a+B+A-b ≤ 1+A+B ≤ 2t]<br>B=0, a≥1: S = 2·t-a-abs(b-A) ≥ 1  [A ≤ 1: abs(b-A) ≤ t-1, a ≤ t]<br>B=0, a=0: S = 2·t-2-A ≥ 1  [A ≤ 1] |
| (1,0) | n13 = t, n24 = a, u02 = 0, w04 = B, n14 = N(b,max(A,1)), n23 = t, u01 = 0, w03 = [A≥1] | A=0: S = a-b ≥ 0  [E1]<br>A≥1, b=0: S = a-(A-B) ≥ -1  [E1]<br>A≥1, b≥1: S = a+B-2-abs(b-A) ≥ -1  [b ≥ A: S = (a-b)+A+B-2, A ≥ 1; b < A: S = a+b-(A-B)-2, a ≥ b ≥ 1] |
| (1,1) | n13 = t+1-max(B,1), n24 = abs(a-A), u02 = 0, w04 = t, n14 = t-b+[B=0]·(2·[b≥1]-1), n23 = t, u01 = 0, w03 = 1 | B≥1: S = abs(a-A)+b-B ≥ -1  [E2]<br>B=0, b≥1: S = abs(a-A)+b-2 ≥ -1<br>B=0, b=0: S = abs(a-A) ≥ 0 |
| (1,2) | n13 = [B=0], n24 = t-a, u02 = 0, w04 = t, n14 = t-b, n23 = t-A, u01 = 0, w03 = 1+pos(B-1) | B≥1: S = (A-B)-(a-b) ≥ -1  [E1]<br>B=0: S = A-(a-b) ≥ -1  [E1] |
| (2,0) | n13 = t, n24 = t, u02 = a, w04 = B, n14 = t+1-max(A,1), n23 = t, u01 = b, w03 = [A≥1] | A≥1: S = (a-b)+A+B-2 ≥ -1  [A ≥ 1]<br>A=0: S = a-b ≥ 0  [E1] |
| (2,1) | n13 = t+1-max(B,1), n24 = t-A, u02 = a, w04 = t, n14 = [B=0], n23 = t, u01 = b, w03 = 1 | B≥1: S = 2·t+(a-b)-A-B ≥ 1  [A+B ≤ 2t-1]<br>B=0: S = 2·t-2+(a-b)-A ≥ 1  [A ≤ 1] |
| (2,2) | n13 = [B=0], n24 = 0, u02 = a, w04 = t, n14 = 0, n23 = t-A, u01 = b, w03 = 1+pos(B-1) | B≥1: S = (a-b)+(A-B) ≥ 0  [E1]<br>B=0: S = (a-b)+A ≥ 0  [E1] |

**Pair (0,4).**  S = u04 + n12 + u13 − u02 − n03 − u14

| zones (z,z') | terms | case: S = simplified formula ≥ bound  [reason] |
|---|---|---|
| (0,T) | u04 = 0, n12 = [E=2], u13 = a, u02 = 0, n03 = pos(b-1)+[E≥1], u14 = [b≥1] | always: S = (a-b)+[E=2]-[E≥1] ≥ -1  [E1] |
| (1,T) | u04 = 0, n12 = b+[E=2], u13 = t, u02 = 0, n03 = t-1+[[a≥1]≠[E≥1]], u14 = max(a,1) | a≥1: S = (b-a)+1+[E=2]-[E=0] ≥ -1  [E1]<br>a=0: S = [E=2]-[E≥1] ≥ -1 |
| (2,T) | u04 = b, n12 = t-[E=2], u13 = t, u02 = a, n03 = t-[E≥1], u14 = t | always: S = (b-a)+[E≥1]-[E=2] ≥ -1  [E1] |

**Pair (1,4).**  S = u14 + u02 + u23 + n03 − u13 − u24 − u01 − n12

| zones (z,z') | terms | case: S = simplified formula ≥ bound  [reason] |
|---|---|---|
| (0,T) | u14 = 0, u02 = 0, u23 = b, n03 = [E≥1], u13 = a, u24 = 0, u01 = 0, n12 = [E=2] | always: S = (b-a)+[E=1] ≥ -1  [E1] |
| (1,T) | u14 = b, u02 = 0, u23 = t, n03 = [E≥1], u13 = t, u24 = a, u01 = 0, n12 = [E=2] | always: S = (b-a)+[E=1] ≥ -1  [E1] |
| (2,T) | u14 = t, u02 = a, u23 = t, n03 = [E≥1], u13 = t, u24 = t, u01 = b, n12 = [E=2] | always: S = (a-b)+[E=1] ≥ 0  [E1] |

**Pair (2,4).**  S = u24 + n03 + u13 − u02 − n12 − u34

| zones (z,z') | terms | case: S = simplified formula ≥ bound  [reason] |
|---|---|---|
| (0,T) | u24 = 0, n03 = [[a≥1]≠[E≥1]], u13 = a·[b≥1], u02 = 0, n12 = [E=2], u34 = pos(b-1) | b≥1: S = (a-b)+1+[E=0]-[E=2] ≥ 0  [E1]<br>b=0: S = [[a≥1]≠[E≥1]]-[E=2] ≥ -1 |
| (1,T) | u24 = a, n03 = M(b)+[E=0], u13 = t, u02 = 0, n12 = [E=2], u34 = t-1+[b≥2] | always: S = a+M(b)+1-[b≥2]+[E=0]-[E=2] ≥ 0  [M(b)+1-[b≥2] ≥ 1] |
| (2,T) | u24 = t, n03 = t-[E≥1], u13 = t, u02 = a, n12 = b+[E=2], u34 = t | always: S = 2·t-a-b-[E≥1]-[E=2] ≥ -1  [a+b ≤ 2t-1] |

<!--/ROWS-->

The cases of each row are exhaustive, so Proposition B is proved: 9 + 9 + 9 + 3 + 3 + 3 = 36 zone pairs, 75 cases.
[test_rows.py: for every pair of prefixes, (1) every term equals the value computed from the word, (2) the signed sum
of the terms is d_H - K, (3) the cases are exhaustive and every simplified formula equals S, (4) S >= the stated bound.]

Reading example, pair (0,2), zones (0,1). Start prefix: P0, zone 0: I_13 = {1..a}, I_14 = {1} if b >= 1,
I_03 = {1..b-1}. End prefix: P2, zone 1: I_03 = {t} + {1..M(B)}, I_13 full, I_34 = {1..t-1} + {t} if B >= 2,
I_24 = {1..A}. So n13 = t - a (R1), u14 = [b>=1], w34 = t-1+[B>=2], n03 = 1 + abs(pos(b-1) - M(B)) (R2; b-1 <= t-2),
w24 = A, and n02 = n12 = u04 = 0. Hence S = (t-a) + [b>=1] + (t-1+[B>=2]) - 1 - abs(pos(b-1) - M(B)) - A.
For b >= 1 and B = 1: M = 1, S = 2t - 1 - a - A - abs(b-2); here A <= B+1 = 2; if b = 1 then a <= 2 and
S >= 2t - 6 >= 0; if b >= 2 then a + (b-2) <= t + (t-1) - 2 = 2t-3 and S >= 2t - 1 - 2 - (2t-3) = 0.

---------------------------------------------------------------------------------------------------------------------

## 6. Proof of the Theorem

Let 0 <= s < p <= L, s = jK+e, p = j'K+e' in the unique representation of Section 2 (so j <= j', e < K or j = 4).

* j = j': the window lies inside one piece (or inside the tail), whose letters are pairwise distinct by (P) (tail:
  03_t != 12_t). So odd[s,p) = p - s, and both conditions hold.
* j' = j+1: Corollary A (Section 4).
* j' >= j+2: the window has length (j'-j)K + e' - e >= 2K - (K-1) = K+1 > k, so we must show odd[s,p) >= k = K-1.
  By the Simplex Lemma odd[s,p) = K + S_{jj'}(e,e'), and S_{jj'}(e,e') >= -1 by Proposition B. QED

**Height function** (summary; this is the function a Lean proof would use): for s = jK+e <= p = j'K+e',

    odd[s,p) = p - s                               if j' = j,
             = K - e + e' - 2 C_j(e,e')            if j' = j+1      ((A1), C_j explicit in (C01)..(C34)),
             = K + S_{jj'}(e,e')                   if j' >= j+2     (S = the simplified formulas of Section 5).

[test_theorem.py: this function equals odd[s,p) for ALL 0 <= s <= p <= L, t = 3..12, and the path property holds.]

---------------------------------------------------------------------------------------------------------------------

## 7. Where t >= 3 is used; t = 2; tightness; what is not proved

* **t >= 3 is used in exactly one row**: pair (0,2), zones (0,1), the two cases with B = 1 (end prefix = 2t+2 or 2t+3
  letters of P2, i.e. just after 03_1 and before/after 24_2), where S >= 2t-6. All other bounds >= -1 hold for
  t >= 2 as written (some rows state a stronger bound like ">= 2" with the remark "t >= 3"; for t = 2 these rows still
  give >= -1).
* **t = 2** (K = 12, k = 11): Sections 1-4 remain true (position table, incidence, Simplex Lemma, State Table, Slot
  Lemma, all term values and simplified formulas), and the only failures of S >= -1 are in that row:
  S = 2t-6 = -2 at (a,b) = (1,0), (A,B) = (2,1) and at (a,b) = (2,1), (A,B) = (2,1), i.e. the windows [1,31) and
  [3,31) with odd = 10 < 11. These are exactly the 2 violations of fam(2). [test_theorem.py, last part]
  Mechanism: the end prefix of P2 has taken 03_t and 03_1 but not yet 34_t, the start prefix of P0 has taken
  14_1 and at most 03_1; n03 = 1 + abs(pos(b-1) - 1) is then as large as the constant 2t - 2 allows only if t >= 3.
* **Tightness.** The bound S = -1 (odd = k exactly) is attained in 25 of the 36 zone pairs, and the stated lower
  bound of the row is attained in 73 of the 75 cases (test_rows.py prints this), so there is no slack to trade.
* **Not proved here / remarks.** Nothing in the Theorem is left open. Not addressed: optimality of the length 4K+2
  (upper bound: PROOF_threshold.md Theorem A, a separate document), and the case t = 2 (the word fails; a (20,11,50)
  path exists by SAT, word_20_11_50.txt). The term columns of the 36 rows were derived by hand from the State
  Table with (R1)-(R3) and are stated without writing out each application of a rule; each of the 276 term entries is
  machine-checked against the word for t = 3..12 (test_rows.py (1)), and each is a one-step consequence of the State
  Table that holds for all t >= 2 (the rules have no hidden t-dependence: the only conditions used are p, q <= t-1 in
  (R2), which hold because b-1 <= t-2, M(B) <= t-1 and B-1 <= t-2).

---------------------------------------------------------------------------------------------------------------------

## 8. Lean plan

Existing infrastructure (ccformal): `cnt T s w c`, `oddc T s w`, `IsPathWord k L T`, PathWalk.lean
(`oddc_snoc_up/down`, `isPathWord_of_walk`, `isPathWord_of_height`, `cnt_three`), and the two previous families
(PathFamEven*.lean, PathFamOdd*.lean) as templates.

Recommended route: **`isPathWord_of_height`** with the explicit H of Section 6 and a down-step predicate read off the
position table. Lean then never has to count coordinates in a window: everything after the occurrence lemmas is
linear arithmetic with case splits. (test_theorem.py checks exactly the three hypotheses `hdn`, `hup`, `hdown` in
this form: dn from the position table only, H(s,x+1) = H(s,x) -+ 1, H(s,x) >= K at down-steps.)

* **L1 word.** `fam2T t : ℕ → ℕ` by cases on piece (p / K), zone, parity and the exceptional columns, exactly the
  zone-column table; coordinate number = (index of the type among 01,02,..,34) * t + (i-1), as in pfam2.py. One
  evaluation lemma per table entry (simp + omega). Parameters: t = τ + 3 or hypothesis `3 ≤ t`; K = 6*t; k + 1 = K.
* **L2 occurrence lemmas** (position table (O)): for each type and each index class, `fam2T p = coord ↔ p ∈ {..}` for
  p < L. Occurrences per coordinate: 13_i four (P0..P3); 03_t four (P0, P2, P3, tail); 03_i (i<t), 14_i, 02_i, 24_i
  three; 04_i, 12_i (two; 12_t three with the tail), 23_i two; 34_i, 01_i one. A `cnt_four` lemma (copy of
  `cnt_three`) is needed for 13_i and 03_t.
* **L3 sign table.** `dn s x` for x = j'K + e' with letter c: with p1 > p2 > p3 the earlier positions of c,
  `dn s x ↔ (p2 < s ∧ s ≤ p1) ∨ s ≤ p3` (same convention as PROOF_family_even.md Section 3). One row per (piece, type,
  index class) = per entry of (O): about 40 rows, each a linear condition in s. (Not written out here; it is a
  mechanical consequence of (O), and test_theorem.py checks the rule "number of earlier occurrences >= s is odd"
  computed from (O) against the word.)
* **L4 height function.** `H s p` by cases on (j, j'): same piece `p - s`; adjacent `K - e + e' - 2*C_j e e'` with
  (C01)..(C34) (define `ev x y := (y+1)/2 - (x+1)/2` with truncated subtraction); non-adjacent `K + S` where S is
  given by the 75 cases of Section 5 in local coordinates a = (r+1)/2, b = r/2 (all formulas are integer-linear with
  `abs`, `max`, indicators; write them over ℤ or split the abs cases). To keep `H : ℕ → ℕ → ℕ`, add K first (H >= K-1
  always in these cases).
  Alternative that avoids the zone-pair case table inside the definition: define the ten index-set SIZES and the
  n_tau of formula (S) as closed forms in e, e' (State Table with (R1)-(R3)) and H := K + signed sum; then the 36 rows
  become `omega` lemmas "H >= K - 1" and the step lemma is "adding the letter at offset e' changes exactly one n_tau
  by one". Either way the arithmetic content is Section 5.
* **L5 step and need lemmas** (`hup`, `hdown`): `H s (x+1) = H s x ± 1` according to `dn s x`, and `dn s x → K ≤ H s x`.
  Because H = odd is already known numerically (test_theorem.py), these are pure `omega` goals after the case split
  (pair of pieces, zone pair, case of the row, parity of r'; zone and piece boundaries x -> x+1 are separate goals:
  r' = 2t-1 -> next zone, e' = K-1 -> next piece, where the formulas of two rows must agree).
  The need lemma is weaker than Proposition B: K <= H before a down-step is "S >= 0 whenever the next letter lowers S".
* **L6** `fam2_isPathWord : 3 ≤ t → IsPathWord (6*t-1) (24*t+2) (fam2T t)` by `isPathWord_of_height`;
  with the upper bound of PROOF_threshold.md Theorem A (now formalized: `path_threshold_A`) this gives P(10t, 6t-1) = 24t+2.

Second route (closer to this proof, more Finset work): formalize the Simplex Lemma itself. Needs (i) `oddc` as a sum
over types of #{i : Odd (cnt ..)}, (ii) for a coordinate with one occurrence per piece, parity of cnt in the window
[jK+e, j'K+e') = [p_c >= e] + (number of pieces strictly between containing the type) + [q_c < e'] mod 2, (iii) the
State Table as `Finset.card` of filters over `range t`. Then Proposition B is 36 `omega` lemmas and the Slot Lemma is
a 10-line injection (`Finset.card_le_card_of_injOn` into the even numbers of [e, e')). I expect route 1 to be faster
because steps (i)-(iii) are new infrastructure, while route 1 reuses the pattern of PathFamOdd*.lean.

Script twins for the Lean definitions: states.py (State Table), positions.py (position table, slots, C_j), rows.py
(S formulas, as strings), test_theorem.py `H` (height function).

---------------------------------------------------------------------------------------------------------------------

## 9. Tests (scripts and data files NOT included in this folder; python3; memory capped at 1.5 GB in common.py; default t = 3..12, env TMAX)

| script | what it checks | result |
|---|---|---|
| test_states.py | Section 1 (P): letters of each piece distinct, types = incidence rule, every index once; Section 3: the State Table (states.py, written from the proof) = index sets of every prefix of every piece and of the tail | OK, 1800 prefixes |
| test_slots.py | Section 1 (O): position table = the word; Section 4: common letters, slot table (p <= phi <= q, slots disjoint), (A1) odd = w - 2C, (A2), explicit formulas (C01)..(C34), path property on all adjacent-piece windows | OK |
| test_simplex.py | Section 2: v_jK xor v_j'K = D_jj' (size K) for 0 <= j < j' <= 4; d_H = K + S for all vertex pairs in different pieces | OK, 144720 vertex pairs |
| test_rows.py | Section 5: every term of every row = value from the word; signs and type lists; signed sum = d_H - K; cases exhaustive; every simplified formula = S; S >= stated bound >= -1 | OK, 73710 prefix pairs, 36 zone pairs, 75 cases |
| test_theorem.py | Section 6: height function H = odd[s,p) for all s <= p, path property; Lean-style walk data (dn from the position table, steps of H, H >= K at down-steps); Section 7: t = 2 | OK, 192120 windows; t = 2: exactly the two windows of Section 7 |
| test_mutation.py (~5 min) | teeth: 1199 mutants (all neighbour swaps, 300 random swaps per t, 7 named swaps of the irregular letters; t = 3, 4, 5); every mutant fails the equalities; every mutant that is not a path word fails an inequality of the proof | OK, see below |
| gen_tables.py | writes the Section 5 tables into this file from rows.py (the strings test_rows.py evaluates) | - |
| `python3 pfam2.py 30` | the Theorem itself by the definition, t = 3..30 | 0 violations |

Mutation test output: `1199 mutants; 1154 are not path words and ALL of them fail an inequality of the proof; 45 remain
path words; all 1199 fail the equalities (state table / row formulas)`. "Inequality of the proof" = a slot condition
p <= phi <= q or (A2), a stated row bound of Section 5, or the distinctness of the letters of a piece (premise of the
same-piece case). Named mutants at t = 3 (violations of the path property / failed equalities / failed inequalities):
P0 14_1 <-> 03_1: 2 / 244 / 5;  P0 03_t <-> 14_2: 1 / 196 / 1;  P2 03_t <-> 13_1: 1 / 86 / 7;  P2 03_1 <-> 34_t: 0 / 120 / 0
(this variant is also a path word at t = 3, and the proof's inequalities happen to hold for it; its State Table differs);
P3 14_1 <-> 13_2: 2 / 274 / 6;  P3 13_1 <-> 03_1: 0 / 224 / 1 (a path word; one stated row bound > -1 fails);
tail swap: 9 / 173 / 12.
