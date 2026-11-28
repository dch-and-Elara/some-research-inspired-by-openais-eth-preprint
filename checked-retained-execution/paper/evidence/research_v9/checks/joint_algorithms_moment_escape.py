#!/usr/bin/env python3
"""Direct source-child moments and completed singleton probes for J7 and J8."""
from collections import Counter, defaultdict, deque
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json

import joint_algorithms as base

OUT = Path(__file__).with_suffix(".json")


def solve(matrix, rhs):
    work = [[F(x) for x in row]+[F(y)] for row,y in zip(matrix,rhs)]
    for k in range(len(work)):
        pivot = next(i for i in range(k,len(work)) if work[i][k])
        work[k],work[pivot] = work[pivot],work[k]
        lead=work[k][k]
        work[k] = [x/lead for x in work[k]]
        for i in range(len(work)):
            if i!=k:
                a=work[i][k]
                work[i]=[x-a*y for x,y in zip(work[i],work[k])]
    return [row[-1] for row in work]


def joint_symbol_law():
    r=4
    weights=Counter()
    pins=Counter()
    for a,s,b in product(range(r),repeat=3):
        if s==a:
            continue
        w=F(1,r*(r-1))*(F(2,r) if b==s else F(r-2,r*(r-1)))
        weights[s,a]+=w
        weights[s,b]+=w
        pins[s,a]+=w
    assert all(weights[s,c]==F(2,r*r) for s,c in product(range(r),repeat=2))
    assert all(pins[s,s]==0 for s in range(r))
    for r in (2,4,8,64):
        assert F(1,r*(r-1))+F(r-2,r*r*(r-1))==F(2,r*r)
    return {"exhaustive_alphabet":4,"analytic_alphabets_checked":[2,4,8,64]}


def logical_v7():
    nodes=[(i,j) for i in range(4) for j in range(4) if i!=j]
    edges=[(a,b) for a,b in combinations(nodes,2) if a[0]==b[0] or a==b[::-1]]
    used=Counter()
    def var(v,j):
        return 1+4*nodes.index(v)+j
    clauses=[(-var(v,0),) for v in nodes]
    for a,b in edges:
        used[a]+=1
        used[b]+=1
        clauses.append((var(a,used[a]),var(b,used[b])))
    clauses.extend([(-var(v,j),var(v,(j+1)%4)) for v in nodes for j in range(4)])
    return nodes, edges, base.physical(clauses)


def large_child_check():
    nodes,edges,(old,subdiv)=logical_v7()
    n=len(nodes)
    pin_ports=[old[i][0][0] for i in range(n)]
    extra=next(ids for ids,tab in old if len(ids)==3 and sum(tab.values())==2)
    source=set(pin_ports+list(extra))
    col_owner={k:j for j,(ids,_) in enumerate(old) for k in ids}
    neighbors=defaultdict(list)
    for e in subdiv:
        if e not in source:
            neighbors[subdiv[e]].append(e)
    mate={}
    def augment(row,seen):
        for e in neighbors[row]:
            col=col_owner[e]
            if col in seen:
                continue
            seen.add(col)
            if col not in mate or augment(subdiv[mate[col]],seen):
                mate[col]=e
                return True
        return False
    for row in neighbors:
        augment(row,set())
    L=8
    equal=[e for e in subdiv if e not in source]
    hpad=((len(equal)+L-1)//L)*L
    n_pack=hpad//L
    matching=list(mate.values())
    assert len(matching)>=2*n_pack
    endpoints=set(matching[:2*n_pack])
    filler=deque([e for e in equal if e not in endpoints]+[None]*(hpad-len(equal)))
    packets=[[matching[i]]+[filler.popleft() for _ in range(L-2)]+[matching[n_pack+i]]
             for i in range(n_pack)]
    assert not filler
    tile_rows=[]
    for k in range(4):
        ports=[pin_ports[3*k+j] for j in range(3)]
        if k<3:
            ports.insert(1,extra[k])
        packet=[None]*L
        for j,e in enumerate(ports):
            packet[2*j]=e
        packets.append(packet)
        tile_rows.append({e:j for j,e in enumerate(ports)})
    # The other orientation in every unequal packet is padding. Empty packets
    # and other all-padding templates are immaterial for this literal sum.
    assert sorted(x for pkt in packets for x in pkt if x is not None)==sorted(subdiv)
    mapped=base.shift(packets,L-1)
    assert all(y not in source for y in mapped.values())
    assert len({subdiv[x] for x in mapped})==len(mapped)
    assert len({col_owner[x] for x in mapped.values()})==len(mapped)
    # The source child consists of its original pin tables and one trivalent
    # equality. Direct enumeration over its original legal assignments,
    # collecting by the unique enabled pin word, computes all actual moments.
    recovered=0
    fixed_patterns=0
    for signs in product((0,1),repeat=n):
        result={}
        for tile in tile_rows:
            indexed=[(p,j) for p,j in tile.items() if p in pin_ports]
            rhs=[]
            for b in range(len(indexed)):
                true_child=0
                for common in (0,1):
                    x={**dict(zip(pin_ports,signs)), **{p:common for p in extra}}
                    true_child+=sum(j**b*x[p] for p,j in tile.items())
                rhs.append(F(true_child,2)-sum(F(j**b,2) for p,j in tile.items() if p in extra))
            decode=solve([[j**b for _,j in indexed] for b in range(len(rhs))],rhs)
            result.update({p:a for (p,_),a in zip(indexed,decode)})
        assert tuple(result[p] for p in pin_ports)==signs
        cover=all(signs[nodes.index(u)] or signs[nodes.index(v)] for u,v in edges)
        via=all(result[pin_ports[nodes.index(u)]] or result[pin_ports[nodes.index(v)]] for u,v in edges)
        assert cover==via
        fixed_patterns+=int(cover)
        recovered+=1
    return {"four_clone_wires":len(subdiv),"actual_shifted_pairs":len(mapped),
            "eligible_pins":n,"actual_nonpin_marginal":"1/2",
            "tiles":len(tile_rows),"child_moments_per_word":n,
            "exact_sign_words_recovered":recovered,"vertex_covers":fixed_patterns}


class Unramified:
    """(Z/2^p)[u]/(u^6+u+1), using literal coordinate polynomial arithmetic."""
    def __init__(self,p):
        self.p=p
        self.mod=1<<p
        self.zero=(0,)*6
        self.one=(1,)+(0,)*5
    def elt(self,v):
        return (base.residue(v,self.mod),)+(0,)*5
    def add(self,a,b):
        m=self.mod
        return tuple((x+y)%m for x,y in zip(a,b))
    def neg(self,a):
        return tuple(-x%self.mod for x in a)
    def sub(self,a,b):
        return self.add(a,self.neg(b))
    def scale(self,c,a):
        return tuple((c*x)%self.mod for x in a)
    def mul(self,a,b):
        if not any(a[1:]):
            return self.scale(a[0],b)
        if not any(b[1:]):
            return self.scale(b[0],a)
        out=[0]*11
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                out[i+j]+=x*y
        for i in range(10,5,-1):
            out[i-6]-=out[i]
            out[i-5]-=out[i]
        return tuple(x%self.mod for x in out[:6])
    def power(self,a,n):
        x=self.one
        while n:
            if n%2:
                x=self.mul(x,a)
            a=self.mul(a,a)
            n//=2
        return x
    def inv(self,a):
        # u^6+u+1 is irreducible modulo two (all nonzero residues tested below).
        x=self.power(a,62)
        for _ in range(self.p.bit_length()):
            x=self.mul(x,self.sub(self.elt(2),self.mul(a,x)))
        assert self.mul(x,a)==self.one
        return x
    def lift(self,bits):
        return tuple((bits>>i)&1 for i in range(6))
    def poly(self,coef,z):
        ans=self.zero
        for x in reversed(coef):
            ans=self.add(self.mul(ans,z),self.elt(x))
        return ans


def kernel_poly(L,t,disp):
    c=base.coeff(L,t)
    p=[c] if t==disp else [F(0),F(2*L)*c/(t-disp)]
    for d in range(-L,L):
        if d in (t,disp):
            continue
        slope=F(2*L,t-d)
        p=[x+y for x,y in zip(p+[0],[0]+[slope*h for h in p])]
    return p


def native_slot_target(r,z,b,slow=False):
    # Two negative/positive switches on the two pin-column ports 0 and 2.
    # Equal-symbol local packets hold all remaining original wires. In the
    # actual unequal packet [0,hole,2,hole] every eligible row crosses.
    L,t=4,3
    packets=[[1,4,5,6],[3,7,None,None],[0,None,2,None]]
    candidates={0:0,2:2}
    old,own=base.physical([(-1,),(-2,),(1,2)])
    nonpin=old[2:]
    kernel={d:r.poly(kernel_poly(L,t,d),z) for d in range(-L+1,L)}
    norm=r.poly(kernel_poly(L,t,t),z)
    A={}
    for port,x in candidates.items():
        d=r.add(r.elt(t+x),r.scale(2*L,z))
        A[port]=r.mul(r.scale(2*L*2**b,r.mul(z,norm)),r.power(r.inv(d),b+1))
    local={p:{} for p in own}
    for packet in packets[:2]:
        for x,p in enumerate(packet):
            if p is not None:
                local[p]={q:kernel[y-x] for y,q in enumerate(packet) if q is not None}
    param=[[(dict(zip(ids,w)),val) for w,val in tab.items() if val] for ids,tab in nonpin]
    total=r.zero
    for assignment in product(*param):
        bits={}
        for subset,_ in assignment:
            bits.update(subset)
        args={}
        for p,edges in local.items():
            value=r.zero
            for q,coef in edges.items():
                if bits[q]:
                    value=r.add(value,coef)
            args[p]=value
        if slow:
            for y in product((0,1),repeat=4):
                for selected,value in A.items():
                    term=value if y[own[selected]] else r.neg(value)
                    for p in own:
                        if p!=selected:
                            term=r.mul(term,args[p] if y[own[p]] else r.sub(r.one,args[p]))
                    total=r.add(total,term)
        else:
            eq=[]
            for k in range(4):
                v,w=args[2*k],args[2*k+1]
                eq.append(r.add(r.sub(r.sub(r.one,v),w),r.scale(2,r.mul(v,w))))
            for selected,coef in A.items():
                k=own[selected]
                term=r.mul(coef,r.sub(r.scale(2,args[selected^1]),r.one))
                for i in range(4):
                    if i!=k:
                        term=r.mul(term,eq[i])
                total=r.add(total,term)
    return total


def true_first_target(b):
    rows=range(4)
    old,own=base.physical([(-1,),(-2,),(1,2)])
    pair=base.shift([[1,4,5,6],[3,7,None,None],[0,None,2,None]],3)
    c=base.coeff(4,3)
    denom=prod((3+x)**(b+1) for x in (0,2))
    total=F(0)
    for assign in product(*[[(dict(zip(ids,w)),v) for w,v in tab.items() if v]
                            for ids,tab in old[2:]]):
        bits={}
        for small,_ in assign:
            bits.update(small)
        args={p:c*bits[pair[p]] if p in pair else F(0) for p in own}
        for y in product((0,1),repeat=len(rows)):
            for selected in (0,2):
                d=F(8*2**b)*c/(3+selected)**(b+1)
                slope=1 if y[own[selected]] else -1
                total+=d*slope*prod((v if y[own[p]] else 1-v)
                                    for p,v in args.items() if p!=selected)
    assert total>0 and (denom*total).denominator==1
    return total,denom


def first_weights(r,nodes):
    vals=[]
    for i,zi in enumerate(nodes):
        v,d,den=r.one,r.zero,r.one
        for j,zj in enumerate(nodes):
            if j!=i:
                d=r.sub(v,r.mul(d,zj))
                v=r.neg(r.mul(v,zj))
                den=r.mul(den,r.sub(zi,zj))
        vals.append(r.mul(d,r.inv(den)))
    return vals


def completed_check():
    p=40
    r=Unramified(p)
    for residue in range(1,64):
        a=r.lift(residue)
        assert r.mul(a,r.inv(a))==r.one
    allnodes=[r.lift(i) for i in range(p+2)]
    actual={(b,j):native_slot_target(r,z,b) for b in (0,1) for j,z in enumerate(allnodes)}
    for j in (0,1,5,19,41):
        for b in (0,1):
            assert actual[b,j]==native_slot_target(r,allnodes[j],b,slow=True)
    modes=[true_first_target(b) for b in (0,1)]
    largest=0
    cases=0
    for start in (0,1):
        ids=range(start,start+p+1)
        coeff=first_weights(r,[allnodes[i] for i in ids])
        for signs in product((0,1),repeat=2):
            powers=[]
            for b in (0,1):
                # Literal source unary tables contracted over their two independent bits.
                src=sum((0**b*x+1**b*y) for x,y in product((0,1),repeat=2)
                        if (x,y)==signs)
                got=r.zero
                for weight,j in zip(coeff,ids):
                    got=r.add(got,r.mul(weight,r.scale(src,actual[b,j])))
                target,denom=modes[b]
                assert got==r.elt(src*target)
                n=r.scale(denom,got)[0]
                if n>=r.mod//2:
                    n-=r.mod
                exact=F(n,denom)
                assert exact==src*target
                largest=max(largest,abs(n).bit_length())
                powers.append(exact/target)
            answer=solve([[1,1],[0,1]],powers)
            assert tuple(answer)==signs
            cases+=1
    return {"physical_CNF_wires":8,"toy_L":4,"dyadic_precision":p,"extension_degree":6,
            "irreducible_residue_units_checked":63,"distinct_actual_probes":len(allnodes),
            "interpolation_points_per_set":p+1,"prescribed_probe_sets":["contains_zero","omits_zero"],
            "literal_target_full_assignment_comparisons":10,"signword_probe_set_decodings":cases,
            "two_graph_only_target_coefficients":[str(d) for d,_ in modes],
            "largest_cleared_numerator_bits":largest}


def main():
    data={"symbol_balance":joint_symbol_law(),"J7":large_child_check(),"J8":completed_check()}
    OUT.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    print(json.dumps(data,sort_keys=True))


if __name__=="__main__":
    main()
