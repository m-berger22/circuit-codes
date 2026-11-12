# The family fam(k, m) is a spread-k path: hand proof for all parameters  (S178)

**Theorem.** Let m >= 0 be even, h = m/2, k odd, K = k+1, and K >= 2m (i.e. k >= 2m-1). Let T = fam(k,m) = A B C D
(defined below), a word of length L = 3K+3m+1 over d = (3K+m)/2 coordinates. Then T is the transition word of a spread-k
path with L edges in Q_d: for all 0 <= s <= e <= L,

    odd[s,e) < k   implies   odd[s,e) = e - s,

where odd[s,e) = number of coordinates occurring an odd number of times in T[s..e-1].

Range: K >= 2m is exactly the range in which the word is DEFINED (C2 uses the A-coordinates m..2m-1 <= k and the
coordinates n_{h+i}, i < h, which need h+i < K/2); there is no further restriction. (pfam.fam raises an IndexError for
k < 2m-1.)

Every numbered statement below is brute-force tested (Section 6 says by which script).

Proof idea in one line: fix the start s and watch the walk e -> odd[s,e). The path property says exactly that the walk
is at height >= K before every down-step (Walk Lemma). For the family, a step j is a down-step iff s lies in one or two
explicit intervals (Sign Table), and after cutting the word into pairs and quadruples of letters the walk height at the
group boundaries is a one-line formula.

---------------------------------------------------------------------------------------------------------------------

## 1. The word and the occurrence table

Coordinates: the A-coordinates 0..k (K of them, K even), n_i = K+i (0 <= i < K/2), N_i = 3K/2+i (0 <= i < h).
Blocks and positions (p = position in T, 0-based):

| block | positions | letters |
|---|---|---|
| A  | p = c, 0 <= c < K | T[c] = c |
| B  | K+2i, K+2i+1, 0 <= i < K/2 | T[K+2i] = 2i, T[K+2i+1] = n_i |
| C1 | 2K+c, 0 <= c < m | T[2K+c] = c |
| C2 | 2K+m+4i+r, 0 <= i < h, r = 0..3 | N_i, n_{h+i}, m+2i, m+2i+1  (r = 0, 1, 2, 3) |
| C3 | 2K+m+c, 2m <= c < K | T[2K+m+c] = c |
| D  | 3K+m+4i+r, 0 <= i < h, r = 0..3 | 2i, n_{h+i}, 2i+1, n_i  (r = 0, 1, 2, 3) |
| D* | 3K+3m | m |

So C = C1 C2 C3 is the word A with the pair (N_i, n_{h+i}) inserted in front of the pair (m+2i, m+2i+1), i < h;
block boundaries: A = [0,K), B = [K,2K), C = [2K,3K+m), D = [3K+m, 3K+3m], L = 3K+3m+1.
All C-blocks and D consist of whole PAIRS (c, c+1) with c even (m and 2m are even, K is even) resp. whole quadruples.

**(O) Occurrence table** (all positions of each coordinate, increasing; read off the table above):

| coordinate | positions |
|---|---|
| even c < m (and c = 0 if m = 0) | c, K+c, 2K+c, 3K+m+2c |
| c = m (m >= 2) | m, K+m, 2K+m+2, 3K+3m |
| even c, m < c < 2m | c, K+c, 2K+2c-m+2 |
| even c >= 2m (c != 0) | c, K+c, 2K+m+c |
| odd c < m | c, 2K+c, 3K+m+2c |
| odd c, m < c < 2m | c, 2K+2c-m+1 |
| odd c > 2m | c, 2K+m+c |
| n_i, i < h | K+2i+1, 3K+m+4i+3 |
| n_{h+i}, i < h | K+m+2i+1, 2K+m+4i+1, 3K+m+4i+1 |
| n_i, m <= i < K/2 | K+2i+1 |
| N_i, i < h | 2K+m+4i |

(For c = m+2i resp. m+2i+1 the C2 position 2K+m+4i+2 resp. +3 is 2K+2c-m+2 resp. 2K+2c-m+1.)
The consecutive differences are the chord list (a)-(f) (gaps between consecutive occurrences, by coordinate class; see test_chords.py), which is correct for m >= 2; for m = 0 the
entry "coordinate m: p = 2K+m+2, g = K+2m-2" must be read as p = 2K, g = K. The minimum gap is K. [test_chords.py]

---------------------------------------------------------------------------------------------------------------------

## 2. The Walk Lemma (any word)

For a start s and a position j >= s call j a **down-step for s** if T[j] occurs an ODD number of times in T[s..j-1],
an **up-step** otherwise. Then odd[s,j+1) = odd[s,j) - 1 resp. + 1, and odd[s,s) = 0.

**Walk Lemma.** A word T of length L is the transition word of a spread-k path iff

    (W)   for all s <= j < L:   j is a down-step for s   implies   odd[s,j) >= k+1.

*Proof.* Fix s and write f(e) = odd[s,e).
(<=) If there is no down-step, f(e) = e-s for all e. Otherwise let j0 be the first down-step. For e <= j0, f(e) = e-s.
For e > j0 we show f(e) >= k by induction: f(j0+1) = f(j0)-1 >= k by (W); and if f(e) >= k, e > j0, then either e is an
up-step and f(e+1) > k, or e is a down-step, so f(e) >= k+1 by (W) and f(e+1) >= k.
(=>) If j is a down-step for s with f(j) <= k then f(j+1) <= k-1 < k, but f(j+1) < (j+1) - s because one step was a
down-step: the window [s, j+1) violates the path property. QED

Link to chord counting (not needed for the proof, useful for the Lean version): the number of down-steps for s in
[s,e) is Q[s,e) = sum_c floor(cnt_c/2) = chords - triples + quads of the window [s,e), and odd[s,e) = (e-s) - 2Q[s,e);
"j is a down-step for s" says that (chords - triples + quads ending at j and starting at >= s) = 1, i.e. exactly the
chord, or the chord, the triple and the quad, lie in the window. [test_walk.py]

---------------------------------------------------------------------------------------------------------------------

## 3. The Sign Table

Let p1 > p2 > p3 be the earlier positions of the coordinate T[j] (as many as exist; at most three by (O)). For s <= j
the number of occurrences in [s,j) is #{i : p_i >= s}, so

    j is a down-step for s   iff   p2 < s <= p1   or   s <= p3

(with the convention that a non-existing p_i makes the corresponding condition read: p2 missing -> "s <= p1";
p3 missing -> second alternative false; p1 missing -> never). Reading p1, p2, p3 off (O) gives, for s <= j:

| # | position j | letter | down-step for s iff |
|---|---|---|---|
| S0 | any j in A; K+2i+1 in B; 2K+m+4i (N_i) | first occurrence | never |
| S1 | K+c, c even, 0 <= c < K | c | s <= c |
| S2 | every position of an EVEN A-letter c in C (C1: 2K+c; C2: 2K+m+4i+2, c = m+2i; C3: 2K+m+c) | c | c < s <= K+c |
| S3 | every position of an ODD A-letter c in C (C1: 2K+c; C2: 2K+m+4i+3, c = m+2i+1; C3: 2K+m+c) | c | s <= c |
| S4 | 2K+m+4i+1, i < h | n_{h+i} | s <= K+m+2i+1 |
| S9 | 3K+m+4i, i < h | 2i | s <= 2i  or  K+2i < s <= 2K+2i |
| S10 | 3K+m+4i+1, i < h | n_{h+i} | K+m+2i+1 < s <= 2K+m+4i+1 |
| S11 | 3K+m+4i+2, i < h | 2i+1 | 2i+1 < s <= 2K+2i+1 |
| S12 | 3K+m+4i+3, i < h | n_i | s <= K+2i+1 |
| S13 | 3K+3m, m >= 2 | m | s <= m  or  K+m < s <= 2K+m+2 |
| S13' | 3K+3m = 3K, m = 0 | 0 | s <= 0  or  K < s <= 2K |

(S2, S3: in C an A-letter c has p1 = K+c, p2 = c if c is even, and p1 = c only if c is odd, whichever C-block it is in.)
[test_positions.py: the table is compared with brute force for every pair s <= j.]

Consequence used all the time: **all steps j >= s inside the block (A, B, C or D) that contains s are up-steps**
Indeed every condition of the table bounds s from above by a position in an EARLIER block than j: S1 (j in B) needs
s <= c < K; S2-S4 (j in C) need s <= K+c < 2K resp. s <= c resp. s <= K+m+2i+1 <= K+2m-1 < 2K; S9-S13' (j in D) need
s <= 2K+m+4i+1 <= 2K+3m-3 < 3K+m, or s <= 2K+m+2 < 3K+m (m >= 2, so K >= 2m >= 4 > 2), or s <= 2K, or less.
Hence, if x1 is the end of the block of s, odd[s,p) = p - s for s <= p <= x1.

---------------------------------------------------------------------------------------------------------------------

## 4. Proof of (W) for the family

Fix s and write V(p) = odd[s,p). We go through the blocks after the block of s **group by group**; the groups are

* B-pairs  (K+2i, K+2i+1), letters (2i, n_i);
* C-pairs  = the two positions of (c, c+1), c even, in C1 or C3; C2-quads (2K+m+4i .. +3), letters
  (N_i, n_{h+i}, c, c+1) with c = m+2i: "prefix (N, n) + C-pair";
* D-quads (3K+m+4i .. +3), letters (2i, n_{h+i}, 2i+1, n_i); and the final letter D* = m at 3K+3m.

For a group we write its sign pattern, e.g. (+,-,-,+), and the height V at its first position; a pattern with height v
is **admissible** if the height before each of its down-steps is >= K (e.g. (+,-,-,+) needs v+1 >= K and v >= K, i.e.
v >= K). (W) for s <=> all groups are admissible (steps in the block of s are up-steps). Throughout sigma denotes the
parity (0 or 1) of the relevant offset (s, t or u).

### Case A: 0 <= s < K.   sigma = s mod 2.   V(K) = K - s.

**B.** By S1 the B-pair i is (+,+) if 2i < s and (-,+) if 2i >= s. There are ceil(s/2) = (s+sigma)/2 pairs of the first
kind and they come first. Hence the height before a pair of the second kind is K - s + 2 ceil(s/2) = K + sigma >= K:
admissible, net change 0.    **V(2K) = K + sigma.**

**C.** By S2, S3 (s < K, so "s <= K+c" holds): an even A-letter c is a down-step iff c < s; an odd c iff c >= s. So the
C-pair (c, c+1) is

* (-,+) if c+1 < s:    needs height >= K;      net 0
* (-,-) if c+1 = s (only for s odd): needs height >= K+1;    net -2
* (+,-) if c >= s:     needs height >= K-1;    net 0,

and by S0, S4 the C2-prefix (N_i, n_{h+i}) is (+,-) (as s < K <= K+m+2i+1): it needs height >= K-1, net 0.
The pairs occur in increasing order of c. So:
 s even: the height is K at every group boundary of C; all needs (>= K, >= K-1) hold.
 s odd: the height is K+1 at every boundary up to and including the start of the pair (s-1, s) [needs >= K, >= K-1,
 >= K+1: ok], and K-1 at every boundary after it, where only (+,-) pairs and (+,-) prefixes remain [need >= K-1: ok].
(If the pair (s-1,s) sits in a C2-quad, the prefix comes first and returns to K+1.)
**V(3K+m) = K - sigma.**

**D.** By S9-S12 (s < K): 2i is a down-step iff s <= 2i; n_{h+i} is an up-step; 2i+1 is a down-step iff 2i+1 < s;
n_i is a down-step. So the D-quad i is

* (+,+,-,-) if 2i+1 < s:   needs height >= K-1;   net 0
* (+,+,+,-) if 2i+1 = s:   needs height >= K-3;   net +2
* (-,+,+,-) if 2i >= s:    needs height >= K;     net 0,

in this order as i increases; D* is a down-step iff s <= m (S13, S13').
 s even: height K at every quad boundary: admissible; D* has height K: admissible.
 s odd, s < m: height K-1 before the quads i < (s-1)/2 [(+,+,-,-): ok], K-1 before quad (s-1)/2 [ok], K+1 before the
 later quads [(-,+,+,-): ok] and before D* [down-step, ok].
 s odd, s > m: all quads are (+,+,-,-) with height K-1 [ok]; D* is an up-step.
Case A is complete.

### Case B: s = K + t, 0 <= t < K.   sigma = t mod 2.   V(2K) = K - t.

Signs (from the table, with s = K+t; S1 is void): in C an even A-letter c is a down-step iff c >= t (S2: c < s holds),
odd A-letters and N_i are up-steps, n_{h+i} (C2) is a down-step iff t <= m+2i+1 (S4). In D: 2i is a down-step iff
t > 2i (S9); n_{h+i} iff t > m+2i+1 (S10); 2i+1 always (S11: 2i+1 < K <= s < 2K <= 2K+2i+1); n_i iff t <= 2i+1
(S12); D* iff t > m (S13, S13').

**C.** C-pair (c, c+1) (in C1 or C3): (+,+) if c < t [net +2], (-,+) if c >= t [needs height >= K, net 0].
C2-quad i, with c = m+2i:

* (+,+,+,+) if t > c+1:     net +4
* (+,-,+,+) if t = c+1:     needs height >= K-1;  net +2
* (+,-,-,+) if t <= c:      needs height >= K;    net 0.

Along C the groups are ordered by c, so the "c < t" groups come first. Let t' = t + sigma (t rounded up to even).

 (B1) t <= m.  C1: t'/2 pairs (+,+), then height K - t + t' = K + sigma, then (-,+) pairs [ok]. C2: all quads are
 (+,-,-,+) (t <= m <= c) with height K + sigma [ok]. C3: all pairs (-,+), height K + sigma [ok].
 **V(3K+m) = K + sigma.**

 (B2) m < t <= 2m.  C1: all h pairs (+,+): V(2K+m) = K - t + m. C2: the quads with c+1 < t, i.e. 2i < t-m-1, are
 (+,+,+,+).  If t is even there are (t-m)/2 of them, and then the height is K - t + m + 2(t-m) = K + t - m >= K; the
 remaining quads are (+,-,-,+) [ok].  If t is odd there are (t-m-1)/2 of them, then the height is
 K - t + m + 2(t-m-1) = K + t - m - 2 >= K - 1, the next quad (c+1 = t) is (+,-,+,+) [needs >= K-1: ok] and leads to
 K + t - m; the remaining quads are (+,-,-,+) with height K + t - m >= K [ok]. (For t = 2m all h quads are (+,+,+,+)
 and the height is K - t + m + 2m = K + t - m as well.)  C3: all pairs have c >= 2m >= t: (-,+) with height K+t-m [ok].
 **V(3K+m) = K + t - m.**

 (B3) t > 2m.  C1, C2: everything is an up-step (c+1 <= 2m-1 < t for the quads): V(2K+3m) = K - t + 3m.
 C3: the pairs c = 2m, ..., t'-2 are (+,+) ((t'-2m)/2 of them), then the height is K - t + 3m + t' - 2m = K + m + sigma,
 and the remaining pairs are (-,+) [ok].   **V(3K+m) = K + m + sigma.**

**D.** D-quad i:

* (+,+,-,-) if t <= 2i:               needs height >= K-1;   net 0
* (-,+,-,-) if t = 2i+1:              needs height >= K+1;   net -2
* (-,+,-,+) if 2i+1 < t <= m+2i+1:    needs height >= K;     net 0
* (-,-,-,+) if t > m+2i+1:            needs height >= K+2;   net -2

(these four conditions are exhaustive and exclusive; in the first two t <= m+2i+1 holds, so n_{h+i} is an up-step).

 (B1) t <= m: start height K + sigma. No quad is of the 4th kind. As i increases: quads with 2i+1 < t are of the 3rd
 kind [height K+sigma >= K: ok]; if t is odd (then t <= m-1) the quad i = (t-1)/2 is of the 2nd kind [height K+1: ok]
 and leads to K-1; the quads with 2i >= t are of the 1st kind, height K - sigma >= K-1 [ok]. D* is an up-step (t <= m).

 (B2) m < t <= 2m: start height K + t - m. The quads of the 4th kind are those with 2i < t-m-1, i.e. the first
 q = floor((t-m)/2) quads; before the j-th of them (j = 0..q-1) the height is K + t - m - 2j >= K + t - m - 2(q-1) >= K+2
 [ok]; after them the height is K + t - m - 2q = K + sigma. All other quads have 2i+1 <= m-1 < t <= m+2i+1: 3rd kind,
 height K + sigma [ok]. D* is a down-step (t > m) with height K + sigma >= K [ok].

 (B3) t > 2m: start height K + m + sigma; all h quads are of the 4th kind (m+2i+1 <= 2m-1 < t); before the j-th the
 height is K + m + sigma - 2j >= K + m - 2(h-1) = K+2 [ok]; after them K + sigma; D* is a down-step with height
 K + sigma [ok].
Case B is complete.

### Case C: s = 2K + u, 0 <= u < K + m.   sigma = u mod 2.   V(3K+m) = K + m - u.

Signs in D (s >= 2K, so only the conditions "s <= ..." with right-hand side >= 2K matter): 2i is a down-step iff
u <= 2i (S9); n_{h+i} iff u <= m+4i+1 (S10); 2i+1 iff u <= 2i+1 (S11); n_i is an up-step (S12);
D* is a down-step iff u <= m+2 (m >= 2, S13) resp. iff u = 0 (m = 0, S13'). So the D-quad i is

* (-,-,-,+) if u <= 2i:                needs height >= K+2;   net -2
* (+,-,-,+) if u = 2i+1:               needs height >= K;     net 0
* (+,-,+,+) if 2i+1 < u <= m+4i+1:     needs height >= K-1;   net +2
* (+,+,+,+) if u > m+4i+1:             net +4

(exhaustive and exclusive; in the first two, u <= 2i+1 <= m+4i+1). As i increases the kinds occur in the order
4th, 3rd, 2nd, 1st.

 (C1) u <= m.  No quad of the 4th kind (u <= m < m+4i+1). The quads with 2i+1 < u are the first a = floor(u/2) ones
 (3rd kind); before the j-th the height is K + m - u + 2j >= K [ok]; after them K + m - u + 2a = K + m - sigma.
 If u is odd, quad (u-1)/2 is of the 2nd kind with height K + m - 1 >= K (m >= u >= 1) [ok], net 0.
 The remaining quads i = ceil(u/2), ..., h-1 are of the 1st kind; before the j-th of them (j = 0, ..., h-ceil(u/2)-1)
 the height is K + m - sigma - 2j >= K + m - sigma - 2(h - ceil(u/2) - 1) = K + u + 2 >= K+2 [ok] (2 ceil(u/2) = u + sigma); after all of them
 the height is K + m - sigma - 2(h - ceil(u/2)) = K + u. D* is a down-step (u <= m <= m+2; for m = 0: u = 0) with
 height K + u >= K [ok].

 (C2) m < u < 3m (s in C2; m >= 2).  No quads of the 1st or 2nd kind (u > m > 2i+1). Let q = #{i < h : u > m+4i+1}.
 The first q quads are (+,+,+,+), the others (+,-,+,+), which need height >= K-1.
 Height after the first q quads: K + m - u + 4q. If q < h then u <= m+4q+1, so this is >= K-1 [ok for quad q], and the
 height only increases afterwards [ok].
 D*: it is a down-step iff u <= m+2, i.e. u in {m+1, m+2}. For u = m+1: q = 0, all h >= 1 quads are of the 3rd kind,
 height before D* = K - 1 + 2h >= K+1 [ok]. For u = m+2: q = 1 (u > m+1), height before D* = K + m - u + 4 + 2(h-1)
 = K + 2h >= K [ok].

 (C3) u >= 3m (s in C3), or m = 0 and u >= 1.  All quads are (+,+,+,+) (u >= 3m > m+4i+1 for i <= h-1), and D* is an
 up-step (m >= 2: u >= 3m > m+2; m = 0: u >= 1). Nothing to check.

 (For m = 0, (C1) covers u = 0 and (C3) covers u >= 1; for m >= 2 the three cases partition 0 <= u < K+m.)
Case C is complete.

### Case D: s >= 3K + m.  All steps are up-steps (Section 3). Nothing to check.

By the Walk Lemma, T is the transition word of a spread-k path with L = 3K+3m+1 edges. Its dimension is the number of
coordinates, K + K/2 + h = (3K+m)/2. QED

Remarks.
1. Tightness: the height K (resp. K+1 before a double down-step) is attained at almost every group, so no slack is
   wasted anywhere; the hypothesis K >= 2m is used only through the definition of the word (C3 = A[2m..K) non-negative
   length, coordinates m+2i+1 <= k, indices h+i < K/2) and in "K > 2" for S13 when m >= 2.
2. Heights at the block ends (useful as a summary and as Lean lemmas):

| s | V(2K) | V(3K+m) | V(3K+3m) (before D*) |
|---|---|---|---|
| s < K, even | K | K | K |
| s < K, odd | K+1 | K-1 | K+1 if s < m, K-1 if s > m |
| s = K+t, t <= m | K-t | K+sigma | K-sigma |
| s = K+t, m < t <= 2m | K-t | K+t-m | K+sigma |
| s = K+t, t > 2m | K-t | K+m+sigma | K+sigma |
| s = 2K+u, u <= m | | K+m-u | K+u |
| s = 2K+u, u > m | | K+m-u | K+m-u+4q+2(h-q),  q = min(h, ceil((u-m-1)/4)) |

---------------------------------------------------------------------------------------------------------------------

## 5. Lean plan  (carried out: PathFamEven*.lean, `famEven_isPathWord`)

Existing infrastructure (ccformal): `cnt T t L c`, `oddc T t L`, `IsPathWord k L T` (Path.lean: `spread : ∀ s w,
s + w ≤ L → oddc T s w < k → oddc T s w = w`), `oddc_cons` (window grows at the LEFT end, GapCriterion.lean).
The proof above grows the window at the RIGHT end; either add the mirror lemma (L1) or mirror the whole proof
(fix e, move s down); (L1) is a 10-line copy of `oddc_cons`.

All statements are written with positions as sums (j = 3K+m+4i+r etc.), no natural subtraction.
Parameters: `K = 2*κ` (κ >= 1), `m = 2*h`, hypothesis `2*h ≤ κ` (i.e. K >= 2m), `k + 1 = K`.

* **L1 `oddc_snoc`**: `oddc T s (w+1) = if Odd (cnt T s w (T (s+w))) then oddc T s w - 1 else oddc T s w + 1`
  (and `Odd (cnt ..) → 1 ≤ oddc T s w`, since the coordinate T (s+w) is itself odd in the window).
* **L2 `isPathWord_of_walk`** (Walk Lemma, direction <= only is needed):
  `(∀ s w, s + w < L → Odd (cnt T s w (T (s+w))) → k + 1 ≤ oddc T s w) → IsPathWord k L T`.
  Proof: for fixed s, by induction on w (with s + w ≤ L) the invariant `oddc T s w = w ∨ k ≤ oddc T s w`
  (up-step: both alternatives survive; down-step: the hypothesis gives oddc >= k+1, so the second alternative holds
  after it). The invariant is exactly `spread`.
* **L3 definition of the word**: `famT κ h : ℕ → ℕ` by cases on the position, exactly the table of Section 1
  (`p < K`, `p < 2K` with parity of `p - K`, ... ; for C2 and D use `(p - base) / 4`, `(p - base) % 4`), plus the
  evaluation lemmas `famT (K+2i) = 2i` (i < κ), `famT (2K+m+4i+1) = K+h+i` (i < h), ... one per row of the table (simp +
  omega). If the alphabet must be a `Fintype`, use `Fin (3κ+h)` and prove `famT p < 3κ+h` for p < L.
* **L4 occurrence lemmas** (table (O)), in the form needed for L5: for each row,
  `famT p = c ↔ p = p0 ∨ p = p1 ∨ ...` for `p < L` (case split over the block of p; omega).
  From these: `cnt famT s w c = (number of the listed positions in [s, s+w))` as a sum of indicators
  (`cnt` is a filter over `range w`; rewrite with the iff, then `Finset.card` of a filter of an explicit set, or directly
  by `cnt_add` splitting the window at the listed positions and `cnt_eq_zero` on the gaps, as in GapCriterion
  `cnt_gap`/`cnt_chain`).
* **L5 sign table**: define `down κ h s j : Prop` by the 11 rows S0-S13' (pure linear conditions in s, with j given in
  the form base+4i+r) and prove, row by row, `s ≤ j → j < L → (Odd (cnt famT s (j - s) (famT j)) ↔ down κ h s j)`
  (state it with `j = s + w` to avoid the subtraction). Each row = L4 for the letter + parity of a sum of <= 3 indicators.
* **L6 height function**: define `H κ h s p : ℕ`/`ℤ` = the claimed value of odd[s,p), piecewise. The cleanest form is
  per group: the value at the group start (formulas of Section 4, = function `claim` of `test_cases.py`) plus the
  partial sum of the group's sign pattern. Prove
    - `H s s = 0`,
    - `H s (j+1) + 1 = H s j` if `down s j`, `H s (j+1) = H s j + 1` otherwise      (step lemma),
    - `down s j → K ≤ H s j`                                                         (need lemma),
  each by the case split of Section 4 (Case A/B/C/D, the sub-case B1/B2/B3, C1/C2/C3, the kind of the group, the
  position inside the group) and `omega`. Alternatively avoid H inside groups: prove for each group kind a lemma
  "if oddc T s (p - s) = v at the group start then the 2 (or 4) steps have this pattern and oddc at the group end is
  v + net", and chain the groups by induction on the pair/quad index i within each block; the inductions are the
  statements "height at the start of pair/quad i = formula(i)" (the bracketed formulas of Section 4):
    - A/B: `V(K+2i) = K - s + 2 min(i, ceil(s/2))`;
    - A/C: `V(pair c) = K + σ` if c < s else `K - σ`;   A/D: `V(quad i) = K - σ` if 2i+1 <= s (= K-1 at 2i+1 = s), `K + σ` after;
    - B/C1: `K - t + c` (c < t), `K + σ` (c >= t);  B/C2: `K - t + m + 4i` (t > m+2i+1), `K + t - m - 2` (t = m+2i+1), `E` (t <= m+2i);
      B/C3: `K - t + m + c` (c < t), `E` (c >= t), with `E = K+σ | K+t-m | K+m+σ` in B1 | B2 | B3;
    - B/D: `K - σ` (t <= 2i), `K + 1` (t = 2i+1), `K + σ` (2i+1 < t <= m+2i+1), `E - 2i` (t > m+2i+1);
    - C/D: `K+m-σ-2(i - ceil(u/2))` (u <= 2i), `K+m-1` (u = 2i+1), `K+m-u+4 min(i,q)+2(i - min(i,q))` (2i+1 < u), q as above.
* **L7** `oddc famT s w = H s (s+w)` by induction on w (L1 + L5 + step lemma); then (W) from the need lemma, and
  **`fam_isPathWord : IsPathWord k (3K+3m+1) (famT κ h)`** by L2.
* **L8** (with the existing upper bound `path_length_bound`): P(d,k) = 3k+3l-2 for k odd, l = m+2 even, d = (3K+m)/2,
  in the common range (upper bound needs k >= 3l-5 = 3m+1; the family exists for k >= 2m-1).

Chord-count formulation (if the Lean proof should follow the GapCriterion pattern instead of L1/L2): the number of
down-steps for s in [s,e) equals `#{x ∈ [s,e) : chord from x inside} - #{triples} + #{quads}` (test_walk.py (ii));
the "down s j" conditions of the Sign Table are exactly "the number of chords/triples/quads ending at j and starting
at >= s is odd", so the same case analysis proves `2 * (chords - triples + quads) ≤ w - k` for w >= k via
"the i-th down-step j_i (i = 0, 1, ...) satisfies j_i >= s + K + 2i", which is (W) rewritten.

---------------------------------------------------------------------------------------------------------------------

## 6. Tests (all in this directory; python3, < 1 min each at the default range)

Default range: all even m <= 16, all odd k with 2m-1 <= k <= 2m+41 (197 pairs; m = 0 included, k >= 1).

| script | what it checks | result |
|---|---|---|
| test_chords.py | chord list (a)-(f) = exactly the consecutive-occurrence pairs (with the m = 0 correction); min gap K | OK, 197 pairs |
| test_positions.py | Section 1: the position table rebuilds fam(k,m); L and d; Section 3: the Sign Table S0-S13' against brute force for EVERY pair s <= j | OK, 197 pairs, 2.2M (s,j); also run for m <= 30, k <= 2m+61: 511 pairs, 16M (s,j) |
| test_walk.py | (i) Walk Lemma on 40000 random words against the vertex definition (12101 valid, 27899 invalid); (ii) down-steps = Q = chords - triples + quads, odd = w - 2Q on the family | OK |
| test_cases.py | Section 4: for every s, the groups claimed by the proof (function `claim`, written from the proof text) tile [end of block of s, L) (coverage = master test), have the claimed sign patterns and the claimed heights; the claimed data imply (W); steps in the block of s are up-steps; plus independent brute-force (W) and famm.check | OK: 26927 starts, 622380 groups; also m <= 40, k <= 2m+81: 268127 starts, 13.2M groups |
