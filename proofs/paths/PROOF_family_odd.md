# The family fam(k, m), m ODD, is a spread-k path: hand proof for all parameters  (S178)

Companion of `PROOF_family_even.md` (m even). Same method (Walk Lemma + Sign Table + heights at group boundaries).

**Theorem.** Let m >= 1 be odd, h = (m-1)/2, k even, K = k+1 (odd), and K >= 2m-1 (i.e. k >= 2m-2). Let
T = fam(k,m) = z A z B C z D (defined below), a word of length L = 3K+3m+1 over d = (3K+m)/2 coordinates. Then T is the
transition word of a spread-k path with L edges in Q_d: for all 0 <= s <= e <= L,

    odd[s,e) < k   implies   odd[s,e) = e - s,

where odd[s,e) = number of coordinates occurring an odd number of times in T[s..e-1].

**Range.** k even, k >= 2m-2 is exactly the range in which the word is DEFINED: C3 = A[2m-1..K) needs 2m-1 <= K, and the
coordinates n_{h+i}, i < h, need 2h-1 < k/2, i.e. k >= 4h = 2m-2 (pfam.fam raises an IndexError for every even
k < 2m-2, m >= 3). There is no further restriction: the word is valid on its whole domain of definition.
For m = 1 this includes the degenerate point k = 0 (T = z 0 z 0 0 z 0), where the statement is vacuous (nothing has
odd < 0) and the proof below still goes through formally; the meaningful range is k >= max(2, 2m-2), k even.
In terms of l = m+2 (odd): k even, k >= 2l-6, L = 3k+3l-2 = 6(d-k)-5, d = (3k+l+1)/2.

Every numbered statement below is brute-force tested (Section 6 says by which script).

---------------------------------------------------------------------------------------------------------------------

## 1. The word and the occurrence table

Coordinates: the A-coordinates 0..k (K of them, K odd), n_i = K+i (0 <= i < k/2), N_i = K+k/2+i (0 <= i < h),
z = K+k/2+h.  Blocks and positions (p = position in T, 0-based):

| block | positions | letters |
|---|---|---|
| z  | 0 | z |
| A  | 1+c, 0 <= c < K | T[1+c] = c |
| z' | K+1 | z |
| B  | K+2+2i, K+3+2i, 0 <= i < k/2 | T[K+2+2i] = 2i, T[K+3+2i] = n_i |
| B* | 2K+1 | k |
| C0 | 2K+2 | 0 |
| C1 | 2K+2+c, 1 <= c < m | T[2K+2+c] = c |
| C2 | 2K+m+2+4i+r, 0 <= i < h, r = 0..3 | N_i, n_{h+i}, m+2i, m+2i+1  (r = 0, 1, 2, 3) |
| C3 | 2K+m+1+c, 2m-1 <= c < K | T[2K+m+1+c] = c |
| z''| 3K+m+1 | z |
| D  | 3K+m+2+4i+r, 0 <= i < h, r = 0..3 | 2i, n_{h+i}, 2i+1, n_i  (r = 0, 1, 2, 3) |
| D* | 3K+3m | m-1 = 2h |

Block boundaries: A = [1,K+1), B = [K+2,2K+2), C = [2K+2,3K+m+1), D = [3K+m+2, 3K+3m], L = 3K+3m+1.
C = C0 C1 C2 C3 is the word A with the pair (N_i, n_{h+i}) inserted in front of the pair (m+2i, m+2i+1), i < h.

**Groups.** Because m and K are odd, the natural pairs are now (c, c+1) with c ODD:
* B = k/2 B-pairs (2i, n_i), then the single letter B* = k;
* C = the single letter C0 = 0, then C-pairs (c, c+1), c odd: (1,2), ..., (m-2, m-1) in C1; C2-quads
  (N_i, n_{h+i}, c, c+1) with c = m+2i odd ("prefix (N, n) + C-pair"); C-pairs (2m-1, 2m), ..., (k-1, k) in C3
  (C3 has K-2m+1 letters, an even number);
* D = h D-quads (2i, n_{h+i}, 2i+1, n_i), then the single letter D* = 2h;
* the three z's are single letters.

**(O) Occurrence table** (all positions of each coordinate, increasing; read off the table above):

| coordinate | positions |
|---|---|
| z | 0, K+1, 3K+m+1 |
| even c < m (c = 0, 2, .., m-1) | 1+c, K+2+c, 2K+2+c, 3K+m+2+2c |
| even c, m < c < 2m-1 | 1+c, K+2+c, 2K+2c-m+3 |
| even c >= 2m | 1+c, K+2+c, 2K+m+1+c |
| odd c < m (c <= m-2) | 1+c, 2K+2+c, 3K+m+2+2c |
| odd c, m <= c < 2m-1 | 1+c, 2K+2c-m+4 |
| odd c >= 2m-1 | 1+c, 2K+m+1+c |
| n_i, i < h | K+3+2i, 3K+m+5+4i |
| n_{h+i}, i < h | K+m+2+2i, 2K+m+3+4i, 3K+m+3+4i |
| n_i, 2h <= i < k/2 | K+3+2i |
| N_i, i < h | 2K+m+2+4i |

(For c = m+2i resp. m+2i+1 the C2 position 2K+m+4+4i resp. +5 is 2K+2c-m+4 resp. 2K+2c-m+3. In D the letter c < m sits
at 3K+m+2+2c for both parities of c, including D* = m-1 at 3K+3m. n_{h+i} sits in B at K+3+2(h+i) = K+m+2+2i.)
The minimum gap between consecutive occurrences is K (e.g. even c: K+2+c -> 2K+2+c). [test_chords.py]

---------------------------------------------------------------------------------------------------------------------

## 2. The Walk Lemma (any word; unchanged from the even case)

For a start s and a position j >= s call j a **down-step for s** if T[j] occurs an ODD number of times in T[s..j-1],
an **up-step** otherwise. Then odd[s,j+1) = odd[s,j) - 1 resp. + 1, and odd[s,s) = 0.

**Walk Lemma.** A word T of length L is the transition word of a spread-k path iff

    (W)   for all s <= j < L:   j is a down-step for s   implies   odd[s,j) >= k+1.

Proof: PROOF_family_even.md, Section 2 (it does not use the word). [test_walk.py]

---------------------------------------------------------------------------------------------------------------------

## 3. The Sign Table

Let p1 > p2 > p3 be the earlier positions of the coordinate T[j] (as many as exist; at most three by (O)). For s <= j

    j is a down-step for s   iff   p2 < s <= p1   or   s <= p3

(a missing p2 makes the first condition "s <= p1", a missing p3 makes the second false, a missing p1 means never).
Reading p1, p2, p3 off (O) gives, for s <= j:

| # | position j | letter | down-step for s iff |
|---|---|---|---|
| S0 | 0; any j in A; K+3+2i in B; 2K+m+2+4i (N_i) | first occurrence | never |
| Z1 | K+1 | z | s = 0 |
| S1 | K+2+c, c even, 0 <= c <= k  (B-pairs and B*) | c | s <= c+1 |
| S2 | every position of an EVEN A-letter c in C (C0, C1: 2K+2+c; C2: 2K+m+5+4i, c = m+2i+1; C3: 2K+m+1+c) | c | c+1 < s <= K+2+c |
| S3 | every position of an ODD A-letter c in C (C1: 2K+2+c; C2: 2K+m+4+4i, c = m+2i; C3: 2K+m+1+c) | c | s <= c+1 |
| S4 | 2K+m+3+4i, i < h | n_{h+i} | s <= K+m+2+2i |
| Z2 | 3K+m+1 | z | 0 < s <= K+1 |
| S9 | 3K+m+2+4i, i <= h  (i = h is D*) | 2i | s <= 2i+1  or  K+2+2i < s <= 2K+2+2i |
| S10 | 3K+m+3+4i, i < h | n_{h+i} | K+m+2+2i < s <= 2K+m+3+4i |
| S11 | 3K+m+4+4i, i < h | 2i+1 | 2i+2 < s <= 2K+3+2i |
| S12 | 3K+m+5+4i, i < h | n_i | s <= K+3+2i |

(S2, S3: in C an A-letter c has p1 = K+2+c, p2 = 1+c if c is even, and only p1 = 1+c if c is odd, whichever C-block it
is in. S9: all even c = 2i <= m-1 lie in C0/C1, so p1 = 2K+2+2i, p2 = K+2+2i, p3 = 1+2i. Unlike the even case there
is no exceptional row for D*: it is row S9 with i = h.)
[test_positions.py: the table is compared with brute force for every pair s <= j.]

Consequence: **every down-step j for s lies in a later block than s**, more precisely:
* s <= K (z or A): the steps j <= K are up-steps (S0);
* K+1 <= s <= 2K+1 (z' or B): the steps j <= 2K+1 are up-steps (Z1 needs s = 0; S1 needs s <= c+1 <= K);
* 2K+2 <= s <= 3K+m (C): the steps j <= 3K+m are up-steps (S2 needs s <= K+2+c <= 2K+1, S3 needs s <= c+1 <= K,
  S4 needs s <= K+m+2+2i <= K+2m-1 <= 2K < 2K+2, using 2m-1 <= K);
* s >= 3K+m+1 (z'' or D): all steps are up-steps (Z2 needs s <= K+1; S9 needs s <= 2K+2+2i <= 2K+m+1 < 3K+m+1;
  S10 needs s <= 2K+m+3+4i <= 2K+3m-3 < 3K+m+1 because K >= 2m-1 > 2m-4; S11 needs s <= 2K+3+2i <= 2K+m;
  S12 needs s <= K+3+2i <= K+m).
Hence odd[s,p) = p - s as long as p does not exceed the end of the range just listed.

---------------------------------------------------------------------------------------------------------------------

## 4. Proof of (W) for the family

Fix s and write V(p) = odd[s,p). We go through the word after the up-range of s **group by group** (groups as in
Section 1). For a group we write its sign pattern, e.g. (+,-,+,-), and the height V at its first position; a pattern
with height v is **admissible** if the height before each of its down-steps is >= K. (W) for s <=> all groups are
admissible. sigma always denotes the parity (0 or 1) of the relevant offset (a, t or u).

There are six cases: Z (s = 0), A (s in A), Z' (s = K+1), B (s in B), C (s in C), D (s >= 3K+m+1).

### Case Z: s = 0.   V(K+1) = K+1.

z' is a down-step (Z1) with height K+1 [ok]: V(K+2) = K.
**B.** S1: s = 0 <= c+1, every even letter is a down-step: all B-pairs are (-,+) with height K [ok], B* is (-) with
height K [ok].  **V(2K+2) = K-1.**
**C.** S2 is false (c+1 < 0 fails), S3 is true, S4 is true: C0 is (+), height K-1 -> K; every C-pair (c odd, c+1) is
(-,+) with height K [ok]; every C2-quad is (+,-,-,+) with height K [ok: K+1 before the first down-step, K before the
second].  V(3K+m+1) = K.   z'' is an up-step (Z2: 0 < s fails).  **V(3K+m+2) = K+1.**
**D.** S9: s <= 2i+1 true; S10: false; S11: false (2i+2 < 0 fails); S12: true. Every D-quad is (-,+,+,-) with height
K+1 [ok, net 0], D* is (-) with height K+1 [ok].

### Case A: s = 1 + a, 0 <= a < K.   sigma = a mod 2.   V(K+1) = K - a.

z' is an up-step (Z1). **V(K+2) = K+1-a.**

**B.** By S1 the even letter c is a down-step iff a <= c. So the B-pair i is (+,+) if 2i < a and (-,+) if 2i >= a.
There are ceil(a/2) = (a+sigma)/2 <= k/2 pairs of the first kind and they come first; so the height before pair i is
K+1-a+2 min(i, ceil(a/2)), which is K+1+sigma >= K before every pair of the second kind [ok, net 0]. B* = k is a
down-step (a <= k) with height K+1+sigma [ok].    **V(2K+2) = K + sigma.**

**C.** By S2, S3 (s <= K, so "s <= K+2+c" holds): an even A-letter c is a down-step iff c < a; an odd c iff c >= a.
C0 = 0 is a down-step iff a > 0. The C-pair (c, c+1), c odd, is

* (+,-) if c+1 < a:    needs height >= K-1;    net 0
* (+,+) if c+1 = a (only for a even, a >= 2):   net +2
* (-,+) if c >= a:     needs height >= K;      net 0,

in this order as c increases, and by S0, S4 the C2-prefix (N_i, n_{h+i}) is (+,-) (s <= K < K+m+2+2i): it needs
height >= K-1, net 0.
 a = 0: C0 is (+): K -> K+1; all C-pairs are (-,+), height K+1 at every group boundary [ok].
 a even, a >= 2: C0 is (-) with height K [ok] -> K-1; the height is K-1 at every boundary up to and including the start
 of the pair (a-1, a) [(+,-) pairs and prefixes need >= K-1: ok], and K+1 at every boundary after it [(-,+) pairs need
 >= K, prefixes >= K-1: ok]. (The pair (a-1, a) exists because 2 <= a <= k; if it sits in a C2-quad the prefix comes
 first and returns to K-1.)
 a odd: C0 is (-) with height K+1 [ok] -> K; no pair has c+1 = a; the height is K at every boundary [(+,-), prefixes:
 need >= K-1; (-,+): need >= K: ok].
V(3K+m+1) = K+1-sigma.   z'' is a down-step (Z2: 0 < s <= K+1) with height K+1-sigma >= K [ok].
**V(3K+m+2) = K - sigma.**

**D.** By S9-S12 (1 <= s <= K): 2i is a down-step iff a <= 2i; n_{h+i} is an up-step; 2i+1 is a down-step iff
2i+1 < a; n_i is a down-step. So the D-quad i is

* (+,+,-,-) if 2i+1 < a:   needs height >= K-1;   net 0
* (+,+,+,-) if 2i+1 = a:   needs height >= K-3;   net +2
* (-,+,+,-) if 2i >= a:    needs height >= K;     net 0,

in this order as i increases; D* = 2h is a down-step iff a <= 2h = m-1 (S9, i = h).
 a even: height K at every quad boundary: admissible; D* has height K [ok whether down or up].
 a odd, a < m (so a <= m-2): height K-1 before the quads i <= (a-1)/2 [(+,+,-,-) and (+,+,+,-): ok], K+1 before the
 later quads [(-,+,+,-): ok] and before D* [down-step, ok].
 a odd, a >= m: all quads are (+,+,-,-) (2i+1 <= m-2 < a) with height K-1 [ok]; D* is an up-step.
(This is literally Case A/D of the even proof with a in the role of s.)  Case A is complete.

### Case Z': s = K+1 (the second z).   V(2K+2) = K+1.

(All of B consists of up-steps, Section 3.)
**C.** S2: c+1 < K+1 <= K+2+c holds for every even c: down-step. S3: K+1 <= c+1 never: odd letters are up-steps. S4:
K+1 <= K+m+2+2i: down-step. So C0 is (-) with height K+1 [ok] -> K; every C-pair (c odd, c+1) is (+,-) with height K
[ok]; every C2-quad is (+,-,+,-) with height K [ok].  V(3K+m+1) = K.  z'' is a down-step (Z2) with height K [ok].
**V(3K+m+2) = K-1.**
**D.** S9: K+1 <= 2i+1 false and K+2+2i < K+1 false: up. S10: K+m+2+2i < K+1 false: up. S11: 2i+2 < K+1 <= 2K+3+2i:
down. S12: K+1 <= K+3+2i: down. Every D-quad is (+,+,-,-) with height K-1 [ok, net 0]; D* is an up-step.

### Case B: s = K+2+t, 0 <= t < K.   sigma = t mod 2.   V(2K+2) = K - t.

Signs (from the table with s = K+2+t): in C an even A-letter c is a down-step iff t <= c (S2: c+1 < s holds), odd
A-letters and N_i are up-steps (S3: s <= c+1 <= K fails), n_{h+i} (C2) is a down-step iff t <= m+2i (S4). z'' is an
up-step (Z2). In D: 2i is a down-step iff t > 2i (S9; this includes D* = 2h: iff t >= m); n_{h+i} iff t > m+2i (S10;
its upper bound s <= 2K+m+3+4i holds); 2i+1 always (S11: 2i+2 < K+2 <= s <= 2K+1 < 2K+3+2i); n_i iff t <= 2i+1 (S12).

**C.** C0 = 0 is a down-step iff t = 0. C-pair (c, c+1), c odd (in C1 or C3): (+,+) if c+1 < t [net +2], (+,-) if
c+1 >= t [needs height >= K-1, net 0]. C2-quad i, with c = m+2i (c+1 = m+2i+1 even):

* (+,+,+,+) if t > c+1:     net +4
* (+,+,+,-) if t = c+1:     needs height >= K-3;  net +2
* (+,-,+,-) if t <= c:      needs height >= K-1;  net 0.

Along C the groups are ordered by c, so the "c+1 < t" groups come first. Let t' = t + sigma (t rounded up to even).

 (B1) t <= m-1.  t = 0: C0 is (-) with height K [ok] -> K-1 = K-1+sigma. t >= 1: C0 is (+) -> K-t+1; the pairs with
 c+1 < t are c+1 = 2, 4, ..., t'-2, i.e. t'/2 - 1 pairs (+,+), after which the height is K-t+1+t'-2 = K-1+sigma (before
 the pair (c, c+1) with c+1 < t the height is K-t+c).  From then on every C1-pair is (+,-), every C2-quad is (+,-,+,-)
 (t <= m-1 < c) and every C3-pair is (+,-), all with height K-1+sigma >= K-1 [ok].
 **V(3K+m+1) = K-1+sigma.**

 (B2) m <= t <= 2m-1.  C0, C1: all up-steps (c+1 <= m-1 < t): V(2K+m+2) = K-t+m. C2: the quads with m+2i+1 < t are
 (+,+,+,+); before quad i of them the height is K-t+m+4i.  If t is odd (t-m even) there are (t-m)/2 of them (<= h),
 and then the height is K-t+m+2(t-m) = K+t-m >= K; the remaining quads are (+,-,+,-) [ok].  If t is even (t-m odd,
 t <= 2m-2) there are (t-m-1)/2 of them, then the height is K+t-m-2 >= K-1, the next quad (c+1 = t) is (+,+,+,-)
 [needs >= K-3: ok] and leads to K+t-m; the remaining quads are (+,-,+,-) with height K+t-m >= K [ok].
 C3: all pairs have c+1 >= 2m > t: (+,-) with height K+t-m [ok].
 **V(3K+m+1) = K+t-m.**

 (B3) t >= 2m.  C0, C1, C2: everything is an up-step (c+1 <= 2m-2 < t for the quads): V(2K+3m) = K-t+3m-2.
 C3: the pairs with c+1 = 2m, ..., t'-2 are (+,+) ((t'-2m)/2 of them; before the pair (c, c+1) the height is
 K-t+m-1+c), then the height is K-t+3m-2+t'-2m = K+m-2+sigma >= K-1, and the remaining pairs are (+,-) [ok].
 **V(3K+m+1) = K+m-2+sigma.**

Write E = V(3K+m+1) (= K-1+sigma | K+t-m | K+m-2+sigma in B1 | B2 | B3).  z'' is an up-step: **V(3K+m+2) = E+1.**

**D.** D-quad i:

* (+,+,-,-) if t <= 2i:               needs height >= K-1;   net 0
* (-,+,-,-) if t = 2i+1:              needs height >= K+1;   net -2
* (-,+,-,+) if 2i+1 < t <= m+2i:      needs height >= K;     net 0
* (-,-,-,+) if t > m+2i:              needs height >= K+2;   net -2

(exhaustive and exclusive, since 2i+1 <= m-2 < m+2i; in the first two n_{h+i} is an up-step).

 (B1) t <= m-1: start height E+1 = K+sigma. No quad is of the 4th kind. As i increases: quads with 2i+1 < t are of the
 3rd kind [height K+sigma >= K: ok]; if t is odd (then t <= m-2) the quad i = (t-1)/2 is of the 2nd kind [height K+1:
 ok] and leads to K-1; the quads with 2i >= t are of the 1st kind, height K-sigma >= K-1 [ok]. D* is an up-step.

 (B2) m <= t <= 2m-1: start height E+1 = K+t-m+1. The quads of the 4th kind are those with 2i < t-m, i.e. the first
 q = ceil((t-m)/2) <= h quads; before the j-th of them (j = 0..q-1) the height is K+t-m+1-2j >= K+t-m+3-2q >= K+2
 [ok] (2q <= t-m+1); after them the height is K+t-m+1-2q = K+sigma (t-m even <=> t odd). All other quads have
 2i+1 <= m-2 < t <= m+2i: 3rd kind, height K+sigma [ok]. D* is a down-step (t >= m) with height K+sigma [ok].

 (B3) t >= 2m: start height E+1 = K+m-1+sigma; all h quads are of the 4th kind (m+2i <= 2m-3 < t); before the j-th
 the height is K+m-1+sigma-2j >= K+m-1-2(h-1) = K+2 [ok]; after them K+sigma; D* is a down-step with height K+sigma
 [ok].
Case B is complete.

### Case C: s = 2K+2+u, 0 <= u < K+m-1.   sigma = u mod 2.   V(3K+m+1) = K+m-1-u.

z'' is an up-step (Z2). **V(3K+m+2) = K+m-u.**
Signs in D (s >= 2K+2, so only the conditions "s <= ..." with right-hand side >= 2K+2 matter): 2i is a down-step iff
u <= 2i (S9; for D* = 2h: iff u <= m-1); n_{h+i} iff u <= m+4i+1 (S10); 2i+1 iff u <= 2i+1 (S11); n_i is an up-step
(S12). So the D-quad i is

* (-,-,-,+) if u <= 2i:                needs height >= K+2;   net -2
* (+,-,-,+) if u = 2i+1:               needs height >= K;     net 0
* (+,-,+,+) if 2i+1 < u <= m+4i+1:     needs height >= K-1;   net +2
* (+,+,+,+) if u > m+4i+1:             net +4

(exhaustive and exclusive; in the first two, u <= 2i+1 <= m+4i+1). As i increases the kinds occur in the order
4th, 3rd, 2nd, 1st.

 (C1) u <= m-1 (s in C0/C1).  No quad of the 4th kind (u < m+4i+1). The quads with 2i+1 < u are the first
 a = floor(u/2) <= h ones (3rd kind); before the j-th the height is K+m-u+2j >= K+1 [ok]; after them
 K+m-u+2a = K+m-sigma.  If u is odd (u <= m-2), quad (u-1)/2 is of the 2nd kind with height K+m-1 >= K [ok], net 0.
 The remaining quads i = ceil(u/2), ..., h-1 are of the 1st kind; before quad i the height is
 K+m-sigma-2(i-ceil(u/2)) >= K+m-sigma-2(h-1-ceil(u/2)) = K+u+3 [ok] (2h = m-1, 2 ceil(u/2) = u+sigma); after all of
 them the height is K+m-sigma-2(h-ceil(u/2)) = K+u+1. D* is a down-step (u <= m-1) with height K+u+1 >= K [ok].

 (C2) u >= m (s in C2 or C3).  No quads of the 1st or 2nd kind (u >= m > 2i+1). Let q = #{i < h : u > m+4i+1}
 = min(h, ceil((u-m-1)/4)). The first q quads are (+,+,+,+), the others (+,-,+,+), which need height >= K-1.
 Height after the first q quads: K+m-u+4q. If q < h then u <= m+4q+1, so this is >= K-1 [ok for quad q], and the
 height only increases afterwards [ok]: before quad i >= q it is K+m-u+4q+2(i-q).  D* is an up-step (u > m-1).

 (For m = 1: h = 0, there are no quads; (C1) is u = 0, D* = 0 is a down-step with height K+1; (C2) is u >= 1.)
Case C is complete.

### Case D: s >= 3K+m+1.  All steps are up-steps (Section 3). Nothing to check.

The six cases cover all starts 0 <= s < L. By the Walk Lemma, T is the transition word of a spread-k path with
L = 3K+3m+1 edges. Its dimension is the number of coordinates, K + k/2 + h + 1 = (3K+m)/2. QED

Remarks.
1. Tightness: the height K (resp. K+1 before a double down-step) is attained in almost every group. The hypothesis
   K >= 2m-1 is used only through the definition of the word (C3 of non-negative length, indices h+i < k/2) and in the
   bound 2K+3m-3 < 3K+m+1 of Section 3.
2. Differences from the even case: (a) the three z's: each is a single step, a down-step only for s = 0 (z') resp.
   1 <= s <= K+1 (z''); they are what makes the two extra cases Z, Z' necessary, and in Cases A, B they shift the
   C-heights by one against the even case while the D-heights come out the SAME (Case A/D, B/D-B1 identical; B2, B3
   identical after the shift E+1); (b) the C-pairs are (odd, even) = (+,-) at height >= K-1 instead of (even, odd) =
   (-,+) at height >= K; (c) D* = m-1 lies in C1, not in C2, so it obeys the general row S9 and Case C has two
   sub-cases instead of three.
3. Heights at the block ends (sigma = parity of a, t, u):

| s | V(2K+2) | V(3K+m+2) (start of D) | V(3K+3m) (before D*) |
|---|---|---|---|
| s = 0 | K-1 | K+1 | K+1 |
| s = 1+a, a even | K | K | K |
| s = 1+a, a odd | K+1 | K-1 | K+1 if a < m, K-1 if a >= m |
| s = K+1 | K+1 | K-1 | K-1 |
| s = K+2+t, t <= m-1 | K-t | K+sigma | K-sigma |
| s = K+2+t, m <= t <= 2m-1 | K-t | K+t-m+1 | K+sigma |
| s = K+2+t, t >= 2m | K-t | K+m-1+sigma | K+sigma |
| s = 2K+2+u, u <= m-1 | | K+m-u | K+u+1 |
| s = 2K+2+u, u >= m | | K+m-u | K+m-u+4q+2(h-q),  q = min(h, ceil((u-m-1)/4)) |

---------------------------------------------------------------------------------------------------------------------

## 5. Unified Lean plan (both parities)

(Proposal only; nothing below has been run through Lean.)

**Parameters.** `κ h : ℕ`, `ε : ℕ` with `ε ≤ 1` (or `ε : Bool` / `Fin 2`), hypothesis `2*h ≤ κ`. Put

    m = 2h + ε,   K = 2κ + ε,   k + 1 = K,   L = 3K + 3m + 1,   d = 3κ + h + 2ε.

ε = 0 is the even family (K >= 2m <=> κ >= 2h), ε = 1 the odd one (K >= 2m-1 <=> κ >= 2h): the SAME hypothesis.
Coordinates: A-letters `c < K`, `n i = K + i` (i < κ), `N i = K + κ + i` (i < h), `z = K + κ + h` (used only if ε = 1).

**One definition** `famT κ h ε : ℕ → ℕ` by cases on the position p, all bases explicit sums:

| condition on p (first that applies) | value |
|---|---|
| p < ε | z |
| p < K + ε | p - ε |
| p < K + 2ε | z |
| p < 2K + 2ε, x = p - (K + 2ε) | x if x even, n (x/2) if x odd |
| p < 2K + 2ε + m, x = p - (2K+2ε) | x |
| p < 2K + 2ε + m + 4h, x = p - (2K+2ε+m) | [N (x/4), n (h + x/4), m + 2(x/4), m + 2(x/4) + 1] at x % 4 |
| p < 3K + m + ε, x = p - (2K+2ε+m+4h) | m + 2h + x |
| p < 3K + m + 2ε | z |
| p < 3K + 3m, x = p - (3K+m+2ε) | [2(x/4), n (h + x/4), 2(x/4)+1, n (x/4)] at x % 4 |
| p = 3K + 3m | 2h |

(3K+m+2ε+4h = 3K+3m; C3 starts at letter m+2h = 2m-ε; for ε = 0 the three "z" rows are empty.) The evaluation lemmas
are stated with positions as sums (`famT (K+2ε+2i) = 2i`, `famT (2K+2ε+m+4i+1) = K+h+i`, ...), so no natural
subtraction appears in any statement. Sanity check to do first in python: this table reproduces pfam.fam for both
parities (it is `word()` of the two test_positions.py with ε inserted).

**Unified occurrence / sign rows.** With ε the two tables (O) and the two Sign Tables coincide row by row:

| row | unified condition (down-step for s) |
|---|---|
| S1  (B, even c at K+2ε+c) | s <= c + ε |
| S2  (even c in C) | c + ε < s <= K + 2ε + c |
| S3  (odd c in C) | s <= c + ε |
| S4  (n_{h+i} in C2 at 2K+2ε+m+4i+1) | s <= K + 2ε + 2(h+i) + 1 |
| S9  (2i in D at 3K+m+2ε+4i, i < h) | s <= 2i + ε  or  K+2ε+2i < s <= 2K+2ε+2i |
| S10 (n_{h+i} in D) | K+2ε+2(h+i)+1 < s <= 2K+2ε+m+4i+1 |
| S11 (2i+1 in D) | 2i+1+ε < s <= 2K+2ε+2i+1 |
| S12 (n_i in D) | s <= K+2ε+2i+1 |
| Z1, Z2 (ε = 1 only) | s = 0;   0 < s <= K+1 |
| S13 (D* = 2h at 3K+3m) | ε = 1: row S9 with i = h.  ε = 0: s <= m or K+m < s <= 2K+m+2 (m >= 2), s <= 0 or K < s <= 2K (m = 0) |

(ε = 0 gives S1-S12 of PROOF_family_even.md, ε = 1 gives Section 3 above; the unified definition and the unified rows are
tested against pfam.fam and brute force for BOTH parities by test_unified.py.) The only genuinely parity-dependent row
is D*, because the letter 2h is in C1 for ε = 1 and is the first C2 letter (or the first C3 letter if h = 0) for ε = 0.

**Which lemmas of the even plan (L1-L8) are shared.**

* **L1 `oddc_snoc`, L2 `isPathWord_of_walk`**: word-independent, shared verbatim (prove once).
* **L3** (definition + evaluation lemmas): ONE definition as above; evaluation lemmas stated once with ε (simp + omega;
  `ε ≤ 1` in context, or `rcases` ε = 0 | 1 first and let omega do both).
* **L4** (occurrence lemmas `famT p = c ↔ p = p0 ∨ ...`): shared with ε for all rows except the z row (ε = 1) and the
  coordinate 2h (two versions). The rows "c < m / m <= c < 2m-ε / c >= 2m-ε" split by parity of c exactly as in (O);
  positions: A: ε+c; B: K+2ε+c; C1: 2K+2ε+c; C2: 2K+2ε+m+4i+2+(c-m-2i); C3: 2K+m+ε+c; D: 3K+m+2ε+2c (c < 2h).
* **L5** (sign table): shared rows S1-S12 as in the table above; Z1/Z2 and S13 separate.
* **L6** (heights): NOT shared in substance. Recommended: a generic lemma
  `walk_of_height (H : ℕ → ℕ → ℕ) (down : ℕ → ℕ → Prop)` saying: if `Odd (cnt T s w (T (s+w))) ↔ down s (s+w)`,
  `H s s = 0`, the step lemma and the need lemma hold, then `IsPathWord k L T` -- this packages L1 + L2 + L7 once.
  Then two instantiations `Heven`, `Hodd`, each proved by its own case split + omega. Partial sharing is possible
  because the grouping can be made uniform: **C-pairs = (c, c+1) with c ≡ ε (mod 2)** (ε = 1 leaves C0 = 0 single),
  and the D-quad kinds/conditions agree after replacing "m+2i+1" by "m+2i+1-ε" (Case B) and "s" by "a = s-ε"
  (Case A, where the D-part is literally identical: heights K-σ / K-1 / K+σ). The group-start formulas for ε = 1:
    - Z:  z' K+1; B-pairs K; B* K; C0 K-1; C-pairs, C2-quads K; z'' K; D-quads, D* K+1;
    - A/B: `V(K+2+2i) = K+1-a+2 min(i, ceil(a/2))`, `V(B*) = K+1+σ`; A/C: `V(C0) = K+σ`,
      `V(pair c) = K-1+σ` (c+1 <= a), `K+1-σ` (c >= a); `V(z'') = K+1-σ`; A/D: as even with a;
    - Z': C0 K+1; pairs, quads K; z'' K; D-quads, D* K-1;
    - B/C: `V(C0) = K-t`; C1 pair: `K-t+c` (c+1 < t), `E` otherwise; C2 quad: `K-t+m+4i` (t > m+2i+1),
      `K+t-m-2` (t = m+2i+1), `E` (t <= m+2i); C3 pair: `K-t+m-1+c` (c+1 < t), `E` otherwise; `V(z'') = E`,
      with `E = K-1+σ | K+t-m | K+m-2+σ` (t <= m-1 | m <= t <= 2m-1 | t >= 2m);
    - B/D: `K-σ` (t <= 2i), `K+1` (t = 2i+1), `K+σ` (2i+1 < t <= m+2i), `E+1-2i` (t > m+2i); `V(D*) = K-σ` (t <= m-1), `K+σ` (t >= m);
    - C/D: `V(z'') = K+m-1-u`; quads as in the even plan (`K+m-σ-2(i-ceil(u/2))`, `K+m-1`,
      `K+m-u+4 min(i,q)+2(i-min(i,q))`), `V(D*) = K+u+1` (u <= m-1), `K+m-u+4q+2(h-q)` (u >= m).
  These are exactly the values returned by `claim` in test_cases.py (tested for every group).
* **L7**: shared (inside `walk_of_height`); final theorem
  `fam_isPathWord : ε ≤ 1 → 2*h ≤ κ → ∀ k, k + 1 = 2*κ + ε → IsPathWord k (3*(2*κ+ε) + 3*(2*h+ε) + 1) (famT κ h ε)`
  (k introduced by an equation, so no subtraction), proved by `rcases` on ε = 0 | 1.
* **L8** (exact value with the upper bound `path_length_bound`): shared statement
  `P(d,k) = 3k+3l-2`, l = m+2, k ≡ l+1 (mod 2), d = (3k+l+1)/2, in the intersection of the family's range
  (κ >= 2h, i.e. k >= 2l-5 for even l, k >= 2l-6 for odd l) with the range of the upper bound (whatever
  `path_length_bound` requires; not examined here).

Estimated extra cost of the odd family once the even one is formal: L3-L5 nothing new if stated with ε from the start,
L6 one more height function with 6 cases (Z and Z' are constant-height and trivial; A/D is the even proof).

---------------------------------------------------------------------------------------------------------------------

## 6. Tests (all in this directory; python3, RLIMIT_AS 800 MB, each < 1 min at the default range)

Default range: all odd m <= 17, all even k with 2m-2 <= k <= 2m+42 (207 pairs; includes the degenerate (k,m) = (0,1)).
Optional arguments `mmax span` (k <= 2m+span).

| script | what it checks | result |
|---|---|---|
| test_chords.py | Section 1: occurrence table (O) = exactly all positions of every coordinate; minimum gap K; fam undefined (IndexError) for even k < 2m-2, 3 <= m <= 39 | OK, 207 pairs (also `41 82`: 903 pairs); 380 undefined pairs |
| test_positions.py | Section 1: the position table rebuilds pfam.fam(k,m); L and d; Section 3: the Sign Table against brute force for EVERY pair s <= j | OK, 207 pairs, 2.58M (s,j); also `31 62`: 528 pairs, 17.7M (s,j) |
| test_walk.py | (i) Walk Lemma on 40000 random words against the vertex definition (12101 valid, 27899 invalid); (ii) down-steps = Q = chords - triples + quads, odd = w - 2Q on the odd family (m <= 9, k <= 2m+22) | OK, 247940 windows |
| test_cases.py | Section 4: for every s, the groups claimed by the proof (function `claim`, written from the proof text) tile [first, L) (coverage), all steps before `first` are up-steps, the groups have the claimed sign patterns and the claimed heights; the claimed data alone imply (W); Remark 3 table (`summary`); plus independent brute-force (W) and pfam.check | OK: 207 pairs, 30015 starts, 769902 groups; also `41 82`: 903 pairs, 282639 starts, 14.66M groups |
| test_unified.py | Section 5: the unified definition `famT κ h ε` (position table with ε) = pfam.fam for both parities, and the unified sign rows (S1-S12 with ε, Z1/Z2, S13) against brute force for every s <= j | OK, 395 pairs (197 even m: h <= 8, max(2h,1) <= κ <= 2h+21; 198 odd m: h <= 8, 2h <= κ <= 2h+21), 4.57M (s,j) |
| test_mutation.py | the tests are not vacuous: 10 single-token mutations of claimed patterns / heights / sign-table rows are each detected (range `7 12`) | OK 10/10 |
