#!/usr/bin/env python3
# S178 pfam.py [mmax] [kmax] : THE FAMILIES. Spread-k path with 3k+3l-2 = 6(d-k)-5 edges in Q_d, d = (3k+l+1)/2, for every l >= 2
# and every k = l+1 (mod 2), k >= 2l-5 (l even) / 2l-6 (l odd).   Write m = l-2, h = floor(m/2), K = k+1.
#   coordinates: A-coordinates 0..k, n_i (i < floor(K/2)), N_i (i < h), and one more coordinate z when m is odd.
#   A = 0 1 .. k
#   B = 0 n_0 2 n_1 4 n_2 ..      (K letters: A with every odd coordinate 2i+1 replaced by n_i)
#   C = 0 .. m-1,  then (N_i, n_{h+i}, m+2i, m+2i+1) for i < h,  then m+2h .. k      (= A with h pairs inserted; K+2h letters)
#   D = (2i, n_{h+i}, 2i+1, n_i) for i < h,  then 2h                                  (4h+1 letters)
#   m even:  T = A B C D            m odd:  T = z A z B C z D
# Found from SAT-guided lexicographically-first maximal words. check() = definition, O(L^2).
import sys
def check(T,k):
    v=[0]
    for c in T: v.append(v[-1]^(1<<c))
    n=len(v)
    for i in range(n):
        for j in range(i+1,n):
            h=(v[i]^v[j]).bit_count()
            if h<k and h!=j-i: return (i,j,h)
    return True
def fam(k,m):
    K=k+1; h=m//2; A=list(range(K)); n=[K+i for i in range(K//2)]; N=[K+K//2+i for i in range(h)]; z=K+K//2+h
    B=[(c if c%2==0 else n[c//2]) for c in A]
    C=list(range(m))
    for i in range(h): C+=[N[i],n[h+i],m+2*i,m+2*i+1]
    C+=A[m+2*h:]
    D=[]
    for i in range(h): D+=[2*i,n[h+i],2*i+1,n[i]]
    D+=[2*h]
    return A+B+C+D if m%2==0 else [z]+A+[z]+B+C+[z]+D
if __name__=='__main__':
    mmax=int(sys.argv[1]) if len(sys.argv)>1 else 12; kmax=int(sys.argv[2]) if len(sys.argv)>2 else 50
    tot=bad=0
    for m in range(mmax+1):
        k0=max(2,2*m-1) if m%2==0 else max(2,2*m-2)
        if (k0+m)%2==0: k0+=1
        ks=[k for k in range(k0,kmax+1,2)]; ok=0
        for k in ks:
            T=fam(k,m); K=k+1
            assert len(set(T))==(3*K+m)//2==max(T)+1 and len(T)==3*K+3*m+1==3*k+3*(m+2)-2
            r=check(T,k); tot+=1
            if r is True: ok+=1
            else: bad+=1; print('BAD',k,m,r)
        print(f'l = {m+2:2d}: k = {ks[0]}..{ks[-1]} step 2: {ok}/{len(ks)} valid' if ks else f'l = {m+2}: no k')
    print('total',tot,'bad',bad)
