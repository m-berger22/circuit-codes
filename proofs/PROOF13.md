# PROOF13 (S171, 2026-11-11): the last equality points with u = jp — the case p = 8, j even

Notation as in PROOF8.md / PROOF10.md: a spread-k circuit code ("coil") of length N in Q_n; K = k+1; l = 2n-3k-1; the excess is
e = N-4k-2l; u = l+(e-4)/2, so N = 4K+2u. T_x = coordinate flipped at position x (x in Z_N). A coordinate used four times is an
F coordinate (its positions: F positions), one used twice a dot. For a position x, x+ is the next position of the same
coordinate, g(x) = x+ - x its gap. Lemma 1, Lemma 2: PROOF.md. The equality condition of Lemma 1 at L = 2K is
(E)  K = u(2u+e)/(2e)   (PROOF8 sec. 4, PROOF10 sec. 6).

The points treated here: for j >= 1 let

        (n, k, N) = (33j, 20j-1, 96j),     K = 20j,  l = 6j+2,  e = 4j,  u = 8j,     N = 4k+2l+4j = Byrnes' value + 4j.

This is the family (n, k+1, N) = j*((6i-1)(i+1), 2i(2i+1), 16i(i+1)) of PROOF10 Cor. 23 at i = 2 ("p = 8": u = jp), which was
left open for even j. (E) holds: u(2u+e)/(2e) = 8j*20j/(8j) = 20j.

**Upper bound** (all j >= 1): K(33j, 20j-1) <= 96j. This is PROOF10 section 1 read with i = 2 (there k-(3l-7) = 2j(2i-3)(i-1) = 2j > 0
and 2k+8-3l-e-e' >= k+5-l-e = 2j(2i+1)(i-1)+2 = 10j+2 > 0; nothing else depends on i).

**Theorem 30.** There is no spread-39 circuit code of length 192 in Q_66. Hence K(66,39) <= 190.   (j = 2)

**Theorem 31.** For every even j >= 4:  K(33j, 20j-1) = 96j  (family 8, section C; j = 4, 6 use a computer check of two explicit codes).

**Corollary 32.** K(33j, 20j-1) = 96j for every j >= 1 except j = 2  (j odd: Theorem 18 of PROOF9.md with p = 8, m = j).
Together with Corollary 28: for even p >= 8 and j >= 1, at k = jp(p+2)/4 - 1, n = j(3p-2)(p+4)/8, a code of length
jp(p+4) = 4k+2l+4j exists (and is then optimal) if and only if p != 6 (mod 8) and (p, j) != (8, 2).
First new values: K(132,79) = 384, K(198,119) = 576, K(264,159) = 768.

Part A is a structure lemma for ALL codes at an equality point whose type-word period does not divide K (the case complementary
to Theorem 24). Part B is Theorem 30, Part C is Theorem 31.

---------------------------------------------------------------------------------------------------------------------------

## Part A. Structure at an equality point with K = P/2 (mod P)

Setting (S): k odd (K even), (E) holds, K >= 2u+2, and C is a spread-k circuit code of length N = 4K+2u in Q_n, n = (3k+l+1)/2.
Then (PROOF10 sec. 6, which restates PROOF8 sec. 0 for general excess e):
 (Z1) every window of length 2K contains exactly K/2 chords (pairs (x, x+) inside the window);
 (Z2) every coordinate is an F coordinate or a dot; dot gaps are >= 2K;
 (Z3) F gaps are >= K and <= K+2u <= 2K-2;
 (Z4) the type word (F/dot pattern) has period P := gcd(2K, N);
 (Z5) if t, t+1 are F positions, there is a triple (x, x+, x++) with x >= t and x++ <= t+2K+1.
Two more standard facts: (W) a window of length K+1 or K+2 contains at most one chord (odd(W) >= k); in particular there are
no adjacent positions s, s+1 with g(s) <= K+1 and g(s+1) = K (both chords would lie in [s, s+K+2)).
(Z6) No two adjacent dots: [t, t+2K-2) contains at most floor((2K-2-k)/2) = K/2-1 chords and [t, t+2K) contains K/2, so a chord
inside [t, t+2K) ends at t+2K-2 or t+2K-1; by (Z2) it is an F chord.

Assume in addition that **P does not divide K**. As P | 2K, P is even and K = h (mod P) with h := P/2; P >= 4 (P = 2 would
divide K). Put M = N/P. "Residue" = position mod P. The type word is a cyclic word of length P; its maximal blocks of F's are
"runs". For F residues a, a+1 the "class a" is the set of the 2M positions with residue a or a+1; it consists of M pairs
(t, t+1), t = a (mod P); a position of residue a has "offset 0", one of residue a+1 "offset 1" (in class a).
A **serve** of the pair (t, t+1) is a triple (x, x+, x++) with x in {t, t+1} and x++ <= t+2K+1. Its gaps are (K,K) [x = t or
t+1], (K,K+1) or (K+1,K) [x = t]. Its last position lies in the pair (t+2K, t+2K+1) of the same class (P | 2K), its middle
position has residue a+h or a+h+1. Call x the "start" and x++ the "end" of the serve.

Two triples of one coordinate that both have gap sum <= 2K+1 are (x, x+, x++) and (x+, x++, x+++) for some x: the four gaps sum
to N > 4K+2, so two disjoint ("opposite") pairs of consecutive gaps cannot both be <= 2K+1.   (T)

**Lemma A1.** For every class a: each pair has exactly one serve; a coordinate has at most one serve of class a; and every
position of the class is the start or the end of exactly one serve of class a. Each pair contains exactly one start and one end.

Proof. If a coordinate had two serves of class a, by (T) they are (x, x+, x++), (x+, x++, x+++), and x+ would be a start of a
class-a serve, so its residue is in {a, a+1}; but it is in {a+h, a+h+1}, and these sets are disjoint (P >= 4, h = P/2). So the
serves of class a belong to distinct coordinates, and each uses two positions of the class (start and end); these position sets
are disjoint. By (Z5) every pair has a serve: at least M serves, using 2M distinct positions of a class with 2M positions. Hence
exactly M serves, one per pair, and starts and ends partition the class. The serve of pair t ends in pair t+2K, and t -> t+2K
permutes the pairs, so every pair contains exactly one end, hence exactly one start. QED

**Lemma A2.** Every run has length 1 or 2.

Proof. Suppose a, a+1, a+2 are F residues. A position y of residue a+1 is a start or end of a class-a serve S and of a
class-(a+1) serve S', both of its coordinate. If S != S', by (T) they are (x, x+, x++) and (x+, x++, x+++), and y would lie in
{x, x++} and in {x+, x+++}: impossible. So S = S': its start and end both have residue a+1 (the only residue common to the two
classes), so its gaps are (K,K) (the gap sum is 0 mod P, and 2K+1 is not).
(i) Every position of residue a, a+1, a+2 is the start or the end of a triple with gaps (K,K) (both ends on its own residue).
For residue a+1 this was just shown. Residue a: let (t, t+1) be a pair of class a. If t+1 is a start (of its (K,K) serve), then
its end t+1+2K is at offset 1 of pair t+2K. If t+1 is an end, then t is the start of the serve of the pair (A1); look at the
offset-1 position y' of the pair t+2K: it is the start or end of a (K,K) triple on residue a+1; if it were the end, that triple
would start at t+1, which is an end and not a start of a class-a serve (A1); so y' is a start, the end in pair t+2K is at offset
0, i.e. the serve starting at t ends at t+2K: gaps (K,K). So all serves of class a have gaps (K,K) and (A1) gives (i) for
residue a. Residue a+2: the same argument for class a+1 with the orientation reversed (the reversed code is a code, and a serve
of the pair t is a reversed serve of the pair t+2K).
(ii) The residues a+h, a+h+1, a+h+2 are F residues (they carry the middle positions of the triples in (i)), so (i) holds for
them as well. Let (x, x+K, x+2K) be one of these triples, of coordinate c, x of residue r in {a, a+1, a+2}. Its middle x+K has
residue r+h, so by (i) it is the start or end of a (K,K) triple of c: that triple is (x+K, x+2K, x+3K) or (x-K, x, x+K). Either
way c has three consecutive gaps K: its positions are x1, x2 = x1+K, x3 = x1+2K, x4 = x1+3K with g(x1) = g(x2) = g(x3) = K,
x1, x3 on one residue ("c is based at r1") and x2, x4 on the antipodal residue r1+h. Its serves are (x1,x2,x3) and (x2,x3,x4):
x1, x2 are starts, x3, x4 are ends.
(iii) So every position of residue a, a+1, a+2, a+h, a+h+1, a+h+2 is an x1, x2, x3 or x4 of such a coordinate. In a pair
(s, s+1) of two adjacent ones of these positions: by (A1) one is a start (x1 or x2), the other an end (x3 or x4); by (W) not
both have gap K, and x1, x2, x3 have gap K; so the end is an x4. Every position of these six residues lies in such a pair, so no
position of these residues is an x3. But a coordinate based at r has its x3 on residue r: no coordinate is based at any of the
six residues; yet a position of residue a belongs to a coordinate based at a or at a+h. Contradiction. QED

By (Z6) and Lemma A2 the type word is a cyclic sequence of runs of length 1 ("1-runs") and 2 ("2-runs") separated by single
dots. For a 2-run {a, a+1} (dots at a-1, a+2) the residues a+h, a+h+1 are not both dots. Say the 2-run (class) a has
   type (i)   if a+h is F and a+h+1 is a dot,
   type (ii)  if a+h is a dot and a+h+1 is F,
   type (iii) if both are F; then {a+h, a+h+1} is a 2-run, "exactly antipodal" to {a, a+1}.

**Lemma A3.** Type (iii) does not occur. In a class of type (i) every serve is x -> x+K -> x+2K+1 with x of residue a; in a
class of type (ii) every serve is x -> x+K+1 -> x+2K+1 with x of residue a. (Start at offset 0, end at offset 1, middle on the
unique F residue among a+h, a+h+1.)

Proof. Type (i): the middle of a serve has residue a+h. From x = t+1 (gaps (K,K)) it would have residue a+h+1; so x = t and
the first gap is K. All starts are at offset 0, so by (A1) all ends are at offset 1: the second gap is K+1.
Type (ii): the middle has residue a+h+1: either x = t with first gap K+1 (then the second is K), or x = t+1 with gaps (K,K). In
both cases the end is at offset 1; so (A1) all starts are at offset 0.
Type (iii): let b = a+h. Every serve of class a has its middle in class b, and conversely (b+h = a mod P). Let c be a coordinate
with a serve S of class a; its middle is a position of class b, hence (A1) the start or end of a serve S' of class b of c;
S' != S, so by (T) c has exactly two serves (y1,y2,y3), (y2,y3,y4): y1, y2 are starts, y3, y4 ends; y1, y3 lie in one of the two
classes, y2, y4 in the other. By (A1) every position of the classes a and b belongs to such a coordinate: there are 4M positions,
so M coordinates. The gaps g1, g2, g3 are in {K, K+1} with g1+g2 <= 2K+1, g2+g3 <= 2K+1. Adding K to a position of class a
(class b) gives a position of class b (class a) with the same offset; adding K+1 raises the offset by 1. So the offsets
(o1,o2,o3,o4) and gap excesses (g1-K, g2-K, g3-K) are one of
      0000 / 000,    1111 / 000,    0111 / 100,    0011 / 010,    0001 / 001
(the gap pattern 101 would give the offsets 0,1,1,2; and o1 = 1 allows only 000).
By (W), if the offset-1 position of a pair has gap K, the offset-0 position has gap >= K+2, so it is a y4 (y1, y2, y3 have gaps
<= K+1); but if that offset-1 position is a y3 (an end), the offset-0 position of its pair is a start (A1), not a y4. So
"o3 = 1 and g3 = K" is impossible: the 2nd, 3rd and 4th patterns are out. In the remaining two (0000/000 and 0001/001) y1, y2,
y3 are at offset 0. Hence all 2M offset-1 positions of the two classes are y4's of the M coordinates: contradiction. QED

Call a 1-run {r} **saturated** if r+h lies in a 2-run.

**Lemma A4.** Let s be the number of saturated 1-runs and r1 the number of 1-runs in one period. Then 2s <= r1. More precisely:
if {r} is saturated, every position of residue r is the middle of a serve whose coordinate has no other serve, and the fourth
position of that coordinate lies on the residue of a 1-run that is not saturated.

Proof. Let {r} be saturated, r+h in the 2-run {a, a+1}. If r+h = a then a+h = r is F and a+h+1 = r+1 is a dot: type (i). If
r+h = a+1 then a+h+1 = r is F and a+h = r-1 is a dot: type (ii). In both cases (A3) all M serves of class a have their middle on
residue r; they belong to M distinct coordinates (A1), so these middles are M distinct positions: all positions of residue r.
Let S = (x, x+, x++) be one of them, c its coordinate. A second serve of c would be (x+, x++, x+++) or (x-, x, x+) by (T), with
x+ as start or end; but starts and ends of serves lie on residues of 2-runs. So S is the only serve of c. Let z be the fourth
position of c. By (A1) every position on a 2-run residue is the start or end of a serve of its coordinate; the only serve of c
has start x and end x++; so z is on a 1-run residue r'. If {r'} were saturated, z would be the middle of a serve of c; the only
serve of c has middle x+ != z. So {r'} is not saturated. The M*s fourth positions are distinct positions on the residues of
the r1-s unsaturated 1-runs: M s <= M (r1-s). QED

Remarks (not needed below). (1) For a class a of type (ii) whose middle residue a+h+1 lies in a 2-run, that 2-run is
b = a+h+1, of type (i), and the coordinates are "ladders" a -> b -> a+1 -> b+1 with gap excesses (1, 0, 1, 2u-2); so 2-runs are
coupled in pairs (a, a+h+1), or attached to a saturated 1-run. (2) These lemmas are a filter on type words (struct/ex4/p8/
wfilter.py adds the windows (W') #{i >= 0 : i+e(t+i) <= D} <= floor(D/2)+1 on the forced excesses): at the p = 8 points it leaves
0, 1, 1, 2, 1, 2, 4 words for j = 2..8, and each surviving word carries a code (lazy SAT without symmetry, tw8.py / tryw.py).
(3) struct/ex4/p8/struc13.py tests A1-A4 on 24 codes of the library at 22 different equality points (families 6, 7, 8,
ladder families, solver codes without any symmetry): all pass.

---------------------------------------------------------------------------------------------------------------------------

## Part B. Proof of Theorem 30   ((n,k,N) = (66,39,192))

K = 40, u = 16, e = 8: (E) holds (16*40/16 = 40), K >= 2u+2 = 34, k is odd. P = gcd(80, 192) = 16 does not divide 40; h = 8,
M = 12. So Part A applies to a hypothetical code. The number of F coordinates is N/2-n = 30 (Z2), so there are 120 F positions:
10 F residues and 6 dot residues per period. By (Z6) and Lemma A2 the type word consists of 6 runs of lengths 1 or 2 with sum
10: four 2-runs and two 1-runs. Up to rotation there are three cyclic arrangements, according to the number (0, 1 or 2) of 2-runs
between the two 1-runs on the shorter side:

  W1 = F.F.FF.FF.FF.FF.   1-runs {0}, {2};  2-runs {4,5}, {7,8}, {10,11}, {13,14}.
       0+8 = 8 and 2+8 = 10 lie in 2-runs: both 1-runs are saturated, s = 2 > r1/2 = 1: contradicts Lemma A4.
  W2 = F.FF.F.FF.FF.FF.   1-runs {0}, {5};  2-runs {2,3}, {7,8}, {10,11}, {13,14}.
       0+8 = 8 and 5+8 = 13 lie in 2-runs: s = 2, contradicts Lemma A4.
  W3 = F.FF.FF.F.FF.FF.   1-runs {0}, {8};  2-runs {2,3}, {5,6}, {10,11}, {13,14}.
       {2,3} and {10,11} are exactly antipodal: type (iii), contradicts Lemma A3.

So no code of length 192 exists; with the upper bound, K(66,39) <= 190 (lengths are even). QED
(Computer confirmation, independent of Part A except for "exactly one serve per FF pair": struct/ex4/p8/tw8.py 2: the lazy SAT
without symmetry is UNSAT for W1, W2, W3 in < 1 s each. Whether K(66,39) = 190 is open.)

---------------------------------------------------------------------------------------------------------------------------

## Part C. Family 8 and the proof of Theorem 31

### C1. The code

Let j = 2i >= 4 be even. P = u = 8j = 16i, h = P/2 = 4j = 8i, K = 20j = 2P+h, N = 96j = 12P = 4K+2u, N/2 = 6P, w := 2u-2.
So K = h (mod P), 2K = 0 = N/2 (mod P), K is even, K > w > u.
The code is invariant under x -> x+P: the gap g(x) depends on the residue r = x mod P. F residues with g = K+e:

  chain D :   h-1 (e=1) -> 0 (e=0) -> h (e=u-5) -> P-5 (e=u+4) -> h-1
  chain E':   h+2 (e=0) -> 2 (e=1) -> h+3 (e=u+4) -> 7 (e=u-5) -> h+2
  ladders :   a (e=1) -> a+h+1 (e=0) -> a+1 (e=1) -> a+h+2 (e=w) -> a      for a in A := {4+8t : 0 <= t <= i-1} u {h+8+8t : 0 <= t <= i-2}
  E runs  :   r (e=u/2), r -> r                                             for r in {7+8t : 1 <= t <= i-2} u {h+11+8t : 0 <= t <= i-3}

(arrows: s(x) = x+g(x) on residues; each step adds h+e mod P; residues mod P). Every chain and ladder has e-sum 2u, i.e. gap sum
4K+2u = N, and an E run has gap N/4 = K+u/2 = 3P: every F orbit of s in Z_N has exactly 4 elements.
All other residues are dots: gap N/2 (the partner has the same residue), except residue 1: gap N/2-2 (partner on residue P-1),
and residue P-1: gap N/2+2 (partner on residue 1). T_x = the orbit of x under s.

One period of the type word, read from residue 4, with the symbols  w / Z / O / m  for the F residues whose INCOMING gap excess
e'(f) := e(s^-1 f) is  w / 0 / 1 / "middle" (u/2, u-5 or u+4)  and '.' for dots:

        [ w Z . m . O O . ]^(i-1)    w Z . m Z . m O .    [ O O . w Z . m . ]^(i-1)    O O . O . Z .
          zone 1 (residues 4 .. h-5)   special 1 (h-4 .. h+4)   zone 2 (h+5 .. P-4)       special 2 (P-3 .. P+3)

(length 8(i-1)+9+8(i-1)+7 = 16i). Explicitly:
  e' = w :  a in A                                  [4+8t (t <= i-1), h+8+8t (t <= i-2)]
  e' = 0 :  Z = {2, h} u {5+8t : t <= i-1} u {h+9+8t : t <= i-2}
  e' = 1 :  O = {0, h+3} u {9+8t, 10+8t : t <= i-2} u {h+5+8t, h+6+8t : t <= i-1}
  middle :  7 (u+4), h-1 (u+4), h+2 (u-5), P-5 (u-5), and the E runs (u/2);  as a set  {7+8t : t <= i-2} u {h-1, h+2} u {h+11+8t : t <= i-2}.
Counts per period: F residues 8 + 4(2i-1) + (2i-4) = 10i = 5j; dots 6i = 3j, no two adjacent; the runs have length 1 or 2, and
the 2-runs are {h-1,h}, {h+2,h+3}, {a,a+1}, {a+h+1,a+h+2} (a in A). Coordinates: 12*(5j/4 + 3j/2) = 33j = n.
With e''(f) := e(s^-1 f) + e(s^-2 f):  e''(f) = 1 exactly for the second elements of the 2-runs (h: 1+0; h+3: 0+1; a+1: 1+0;
a+h+2: 0+1); all other values are >= u-5 (u-5 at residues 2 and P-5; u+5, u, 2u-1, w+1 otherwise).
(struct/ex4/p8/p8fam.py + p8build.py build the code; lem13.py checks this table and every step below.)

### C2. Reduction

All gaps are >= K (dots: N/2-2 >= K). A window and its complement have the same odd coordinates, and a window of length <= k
has distinct coordinates; so it suffices to show odd(W) >= k for W = [t, t+L), K <= L <= N/2 = 2K+u. Write L = K+y,
0 <= y <= K+u.
Dots in W: both positions of a dot lie in W only if the gap is <= L-1 <= N/2-1, i.e. the dot starts on residue 1 (gap N/2-2)
at a position x >= t with x+N/2-2 <= t+L-1. So the number of dots occurring twice is
   Dd(t,y) = 1 if (y = K+u-1 and t = 1 mod P) or (y = K+u and t = 0 or 1 mod P),  and 0 otherwise.
F coordinates: three consecutive gaps sum to at least N-(K+w) = 3K+2 > N/2, so an F coordinate occurs at most 3 times in W.
With P(t,y) = number of F chords (x, s x) inside W and T(t,y) = number of F triples (x, s x, s^2 x) inside W:
odd(W) = L - 2(P - T + Dd), and the claim is

   (*)    P(t,y) - T(t,y) + Dd(t,y) <= floor((y+1)/2)     for all t and 0 <= y <= K+u.

As in PROOF7 sec. 3: a chord starting at x lies in W iff the point m = x+e(x) = s(x)-K satisfies m-e(x) >= t and m < t+y;
m runs once over M := F-K (= F+h mod P), and e(x) = e'(m+K):
   (1)    P(t,y) = #{ m in M n [t,t+y) : m - e'(m+K) >= t }.
A triple starting at x lies in [t, t+2K+d) iff the point f = x+e(x)+e(s x) = s^2(x)-2K satisfies f-e''(f) >= t and f < t+d
(f has the residue of s^2(x); x -> f is a bijection of the F positions):
   (2)    T(t,K+d) = #{ f in F n [t,t+d) : f - e''(f) >= t }    (d >= 1);   T = 0 for y <= K+1.

### C3. Proof of (*) for y >= w

(A1) P(t,K) = K/2 for all t. Let X(t) = #{x in F : x < t <= x+e(x)}. A point m of M n [t,t+y) fails the condition in (1) iff
its x is < t; and every x counted in X(t) has m = x+e(x) <= t-1+w < t+y when y >= w. So P(t,y) = |M n [t,t+y)| - X(t) for
y >= w (K >= w). X(t+1)-X(t) = [t in F] - [t in M] (x -> x+e(x) is a bijection F -> M; the chords with e = 0 cancel) and
|M n [t+1,t+1+K)| - |M n [t,t+K)| = [t+K in M] - [t in M] = [t in F] - [t in M] (t+2K = t mod P). So X(t) - |M n [t,t+K)| is
constant; summing over a period, sum X = sum of e over the F residues = (2i+1)*2u + (2i-4)*u/2 = 5iu = 20j^2 and
sum |M n [t,t+K)| = K*5j = 100j^2: the constant is -80j^2/P = -10j = -K/2.

(A2) w <= y <= K: P(t,K) - P(t,y) = |M n [t+y,t+K)| >= floor((K-y)/2) (M = F+h has no two adjacent non-members). So
P(t,y) <= K/2 - floor((K-y)/2) = ceil(y/2) = floor((y+1)/2). T = Dd = 0 (y <= K < K+u-1).

(B) y = K+d, 1 <= d <= u. P(t,K+d) = K/2 + |M n [t+K,t+K+d)| = K/2 + |F n I|, I = [t,t+d). Let F' = F minus the second
elements of the 2-runs; F' has no two adjacent members (runs have length <= 2) and |F'| = 10i-4i = 6i per period. By (2),
T >= #{f in F n I : e''(f) = 1, f-1 >= t} = |(F \ F') n I| - [t in F \ F']. Hence
        P - T + Dd <= K/2 + |F' n I| + [t in F \ F'] + Dd.
If Dd = 0: when t is not in F \ F', |F' n I| <= ceil(d/2); when t is in F \ F', t+1 is a dot and t is not in F', so
|F' n I| = |F' n [t+2,t+d)| <= ceil(d/2)-1 (this also holds for d = 1). In both cases P-T+Dd <= K/2+ceil(d/2) = floor((K+d+1)/2).
If Dd = 1: d is u-1 or u and t is 0 or 1 mod P; residue 1 is a dot and residue 0 is in F'; so [t in F \ F'] = 0, and
|F' n I| <= 6i (I is at most one period) <= 8i-1 = ceil(d/2)-1. Again P-T+Dd <= K/2+ceil(d/2).

### C4. Proof of (*) for 0 <= y <= w   (T = Dd = 0)

By (1) with f = m+K, t' = t+K, J = [t', t'+y):   P(t,y) = C(J) := #{ f in F n J : f - e'(f) >= t' }.
Points with e' = w are never counted (y <= w). Let Q = Z u O, Mid = the middle residues, F0 = Q u Mid. A point of Z is always
counted, a point of O iff it is not t', a middle point f only if f >= t'+h (all middle values are >= u/2 = h).

**Claim 1.** For every interval J = [t', t'+y):  |Q n J| - [t' in O] <= ceil(y/2).
Proof. The only adjacent pairs of Q are the "OO pairs" (9+8t, 10+8t) (t <= i-2) and (h+5+8t, h+6+8t) (t <= i-1); all start at
an odd residue (h is even). Cut J into consecutive blocks {t',t'+1}, {t'+2,t'+3}, .. (the last possibly a single position).
If t' is even, no block is an OO pair: every block has at most one point of Q, so |Q n J| <= ceil(y/2).
Let t' be odd. The blocks start at odd residues. Call a block (r, r+1), r odd, "empty" if it has no point of Q. Empty are
   (3+8t, 4+8t) for t <= i-1 [dot, w];   (7+8t, 8+8t) for t <= i-2 [middle, dot];   (h+1, h+2) [dot, middle];
   (h+7+8t, h+8+8t) and (h+11+8t, h+12+8t) for t <= i-2 [dot, w] and [middle, dot].
Going around the cycle, between two consecutive OO pairs there is an empty block: (11+8t, 12+8t) between the OO pairs at 9+8t
and 17+8t; (h-5, h-4) between h-7 and h+5; (h+7+8t, h+8+8t) between h+5+8t and h+13+8t; (3,4) between P-3 and P+9.
So if J contains m >= 1 full OO blocks, it contains at least m-1 empty blocks and |Q n J| <= ceil(y/2)+1, with equality only
if no empty block of J precedes the first OO block (r1, r1+1) of J. The last empty block before r1 starts at r0 = r1-2
[(7+8t, 8+8t) before 9+8t; (h+11+8t, h+12+8t) before h+13+8t] or, for r1 = h+5, at r0 = h+1. If it is not in J, then t' is odd
with r0 < t' <= r1: t' = r1, or (r1 = h+5) t' = h+3; in each case t' is in O, and [t' in O] = 1. QED

Case 1 <= y <= h (y = 0 is trivial): no middle point is counted, so C(J) = |Q n J| - [t' in O] <= ceil(y/2) by Claim 1.

Case h < y <= w, i >= 4. Let U be the number of points of F0 n J that are not counted; C(J) = |F0 n J| - U.
(a) |F0 n J| <= y/2 + 3. Let delta(r) = +1 for r in F0 and -1 otherwise, and Lam(x) = sum of delta over [4, x). Reading the
symbol word: in zone 1 the partial sums of a block are -1,0,-1,0,-1,0,1,0; special 1: -1,0,-1,0,1,0,1,2,1; then in zone 2 each
block gives 2,3,2,1,2,1,2,1; special 2: 2,3,2,3,2,3,2. So for x in [4, P+4]: -1 <= Lam(x) <= 3, Lam(x) <= 1 for x <= h+3, Lam(x) >= 1 for
x >= h+4, and Lam(x+P) = Lam(x)+2. For a < b with b-a < 2P write a = a0+P*al, b = b0+P*be with
a0, b0 in [4, P+4). If b0 >= a0 then be-al <= 1 and Lam(b)-Lam(a) <= 4+2. If b0 < a0 then be-al <= 2 and
Lam(b0)-Lam(a0) <= 2 (if Lam(b0) >= 2 then b0 >= h+4, so a0 > h+4 and Lam(a0) >= 1; if Lam(b0) <= 1 use
Lam(a0) >= -1), so Lam(b)-Lam(a) <= 2+4. Hence 2|F0 n J| - y <= 6.
(b) U >= i-1 >= 3: the middle points in [t', t'+h) lie in J (y > h) and are not counted. The middle residues are 7+8t (t <= i-2), h-1, h+2,
h+11+8t (t <= i-2); the cyclic gaps between consecutive ones are 8, except one gap 3 (h-1 to h+2), one gap 9 (h+2 to h+11) and
one gap 12 (P-5 to P+7). An interval with exactly m middle points is shorter than the sum of some m+1 consecutive gaps
<= 8(m+1)+1+4 (for m+1 <= 2i, the number of gaps in a period, so that the gaps 9 and 12 occur at most once; if m >= 2i there
is nothing to show). So h = 8i < 8m+13, m >= i-1.
Hence C(J) <= y/2 + 3 - 3 <= ceil(y/2).

Case h < y <= w, i = 2, 3 (j = 4, 6): the inequality C(J) <= ceil(y/2) is checked for all t', y by lem13.py; independently
the two codes are verified from the definition (all pairs of positions) by p8build.py and by snake/check.py
(codes/fam8_132_79_384.txt, fam8_198_119_576.txt).

C3 and C4 give (*) for all t, y: the walk is a spread-k circuit code of length 96j in Q_{33j}; with the upper bound,
K(33j, 20j-1) = 96j. QED

### Checks

p8build.py: definition (all pairs), every even j = 4..60: VALID. snake/check.py: VALID for j = 4, 8, 12 (codes/fam8_*).
lem13.py JMAX: the table of C1 (symbol word, e', e''), (1), (2), the formula P = K/2 + |F n I|, Dd, (A1), (*) against direct
chord/triple/dot counts (all windows for j <= 6, a sample of 1/11 beyond), Claim 1 for all t' and y < 2P, bound (a), bound (b),
and C(J) <= ceil(y/2) for all t', y <= w: all ok for j = 4..20.
How it was found: Part A as a filter on type words (wfilter.py) left one word at j = 4 and at j = 6; lazy SAT without symmetry
found codes on them in seconds; with the shift-P symmetry imposed the j = 6 solution was reflection-symmetric about residue 1,
the F skeletons at j = 4, 6 differ by repeating period-8 blocks, and a solver completion of the skeleton with dot gaps within
2 of N/2 (j = 4, 6, 8) was "all antipodal except one pair". (Referee: the variant with ALL dots antipodal is also a code at
j = 4, 6; then Dd = 0 throughout. Not used here.)

## Referee report (#27, S171)

A fresh AI agent, working from this text (own generator and checkers in theory/referee27/: gen.py, tables.py, parta.py,
mutate2.py; the author's scripts were not read): PASS WITH FIXES, no mathematical error in Theorems 30, 31, Corollary 32; five
wording fixes (applied: the pattern 101 in Lemma A3, "lie in J" in C4 (b), y >= 1 in C4, the remark on the dots, the citation of
Z1-Z5). Part A re-derived by hand, lemma by lemma: correct. Its checks: the code rebuilt from C1 alone, all-pairs definition
for even j = 4..20; every table and inequality of C1-C4 for j = 4..26 (all windows for j <= 8); Z1-Z6 and A1-A4 on 44 library
codes + 9 family-8 codes; negative control (40/40 mutated codes rejected). Not checked: remarks (1)-(3) of Part A, j > 26.
NO HUMAN HAS READ THIS.
