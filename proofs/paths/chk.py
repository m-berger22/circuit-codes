def check(w,k,verbose=False):
    vs=[0]
    for c in w: vs.append(vs[-1]^(1<<c))
    bad=[]
    L=len(w)
    for i in range(L+1):
        for j in range(i+1,L+1):
            dh=bin(vs[i]^vs[j]).count('1')
            if (j-i<k and dh!=j-i) or (j-i>=k and dh<k): bad.append((i,j,dh))
    return bad
