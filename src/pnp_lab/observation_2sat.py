"""Decide complements of codimension <=2 affine events via 2SAT and k parities.

k is the number of independent consistency constraints on our selected linear
observations. Exact decision in polynomial space and K^O(k) time. A work limit
on the nonempty seed subsets can yield UNKNOWN. No survivor count is supplied.
"""
from itertools import combinations
from .overlap_lattice import _point, _rref


def _rank(rows):
    basis={}
    for x in rows:
        while x:
            i=x.bit_length()-1
            if i not in basis:
                basis[i]=x; break
            x^=basis[i]
    return len(basis)


def _plan(n,events):
    if type(n) is not int or n<0:raise ValueError('Expected a nonnegative explicit dimension.')
    raw=[];einfo={};original={};forced=set();freq={}
    if isinstance(events,(str,bytes)):raise ValueError('Invalid event sequence.')
    try:
        for event in events:
            if isinstance(event,(str,bytes)):raise ValueError('Invalid event.')
            rows=[]
            for m,b in event:
                if type(m) is not int or m<0 or m.bit_length()>n or type(b) not in (int,bool) or b not in (0,1):
                    raise ValueError('Invalid parity equation.')
                rows.append((m<<1)|int(b))
            raw.append(tuple(rows))
            canonical=_rref(rows)
            if canonical is None or canonical in einfo:continue
            if len(canonical)>2:raise ValueError('Observation 2SAT requires each nonempty event to have codimension at most two.')
            if len(canonical)==2:
                (u,b),(v,c)=[(r>>1,r&1) for r in canonical]
                plane=tuple(sorted((u,v,u^v)));values={u:b,v:c,u^v:b^c}
                if plane not in original:
                    # Baseline uses two original independent masks. This
                    # gives a deficiency no larger than blindly using all
                    # input observations, including for overlapping planes.
                    pair=tuple(dict.fromkeys(r>>1 for r in rows if r>>1))[:2]
                    original[plane]=pair
                    for w in plane:freq[w]=freq.get(w,0)+1
            elif canonical:
                u,b=canonical[0]>>1,canonical[0]&1
                plane=(u,);values={u:b};forced.add(u)
            else:plane=();values={}
            einfo[canonical]=(plane,values)
    except TypeError as err:raise ValueError('Expected an iterable of events and rows.') from err
    mandatory=forced|{w for w,c in freq.items() if c>1}
    plans=[('original_equations',original)]
    forced_completion={}; feasible=True
    for p in sorted(original):
        shared=[w for w in p if w in mandatory]
        if len(shared)>2:feasible=False;break
        forced_completion[p]=tuple((shared+[w for w in p if w not in mandatory])[:2])
    if feasible:plans.append(('mandatory_completion',forced_completion))
    used=set(forced);greedy={}
    for p in sorted(original,key=lambda p:(-sum(freq[w] for w in p),p)):
        greedy[p]=tuple(sorted(p,key=lambda w:(w not in used,-freq[w],w.bit_count(),w))[:2]);used.update(greedy[p])
    plans.append(('shared_lines_greedy',greedy))
    def forms(plan):return set(forced).union(*(set(x) for x in plan.values()))
    name,plan=min(plans,key=lambda pair:len(forms(pair[1])))
    obs=tuple(sorted(forms(plan)));index={v:i for i,v in enumerate(obs)}
    clauses=[]
    for p,vals in einfo.values():
        clauses.append(tuple((index[w],vals[w]) for w in (plan[p] if len(p)==3 else p)))
    rank=_rank(obs);common=feasible and len(forms(forced_completion))==rank
    if common!=(len(obs)==rank):raise AssertionError('Incorrect simultaneous-basis classification.')
    return raw,obs,clauses,dict(distinct_forms=len(obs),rank=rank,deficiency=len(obs)-rank,
                                input_basis_forms=len(forms(original)),common_basis=common,
                                choice_plan=name,distinct_planes=len(original),
                                mandatory_lines=len(mandatory),observation_forms=list(obs))


def _base(K,clauses):
    edges=[[] for _ in range(2*K)];back=[[] for _ in range(2*K)]
    def arrow(a,b):edges[a].append(b);back[b].append(a)
    for c in clauses:
        if not c:return None
        u=2*c[0][0]+c[0][1]
        if len(c)==1:arrow(u,u^1)
        else:
            v=2*c[1][0]+c[1][1];arrow(u,v^1);arrow(v,u^1)
    order=[];seen=set()
    for i in range(2*K):
        if i in seen:continue
        seen.add(i);stack=[(i,0)]
        while stack:
            v,j=stack[-1]
            if j==len(edges[v]):order.append(v);stack.pop();continue
            stack[-1]=(v,j+1);w=edges[v][j]
            if w not in seen:seen.add(w);stack.append((w,0))
    cid=[-1]*(2*K);color=0
    for v in reversed(order):
        if cid[v]!=-1:continue
        cid[v]=color;queue=[v]
        while queue:
            for w in back[queue.pop()]:
                if cid[w]==-1:cid[w]=color;queue.append(w)
        color+=1
    if any(cid[2*i]==cid[2*i+1] for i in range(K)):return None
    p=sum(1<<i for i in range(K) if cid[2*i+1]>cid[2*i])
    if any(all(((p>>i)&1)==b for i,b in c) for c in clauses):raise AssertionError('Invalid SCC model.')
    return p


def _checks(forms):
    rows={};checks=[]
    for i,a in enumerate(forms):
        tag=1<<i
        while a:
            piv=a.bit_length()-1
            if piv not in rows:rows[piv]=a,tag;break
            r,t=rows[piv];a^=r;tag^=t
        if not a:checks.append(tag)
    return checks


def solve_observation_2sat(n,events,*,max_subsets=None):
    """Return a source parameter point, UNSAT, or subset-budget UNKNOWN.

    Events are forbidden conjunctions of parity equations. max_subsets counts
    enumerated NONEMPTY generator subsets, not normalization, SCCs, closure
    preprocessing, or the initial 2SAT model. The latter can decide k=0, an
    inconsistent 2CNF relaxation, or a coincidentally consistent model without
    enumeration. Different candidate local bases represent exactly the same
    events; only the smallest tried basis is used (not necessarily optimal).
    """
    if max_subsets is not None and (type(max_subsets) is not int or max_subsets<0):
        raise ValueError('Expected a nonnegative subset budget.')
    raw,forms,clauses,out=_plan(n,events);K=len(forms);k=out['deficiency'];checks=_checks(forms)
    if len(checks)!=k:raise AssertionError('Incorrect parity-check count.')
    out.update(status='UNKNOWN',reason=None,witness=None,observation_witness=None,
               input_events=len(raw),effective_clauses=len(clauses),parity_checks=checks,
               subsets_tested=0,unique_closures_tested=0,eligible_generators=None,
               max_subsets=max_subsets,seed_indices=None)
    def good(y):return all((t&y).bit_count()%2==0 for t in checks)
    def success(y,seed,why):
        sol=_rref((a<<1)|((y>>i)&1) for i,a in enumerate(forms))
        if sol is None:raise AssertionError('Parity-consistent observations did not lift.')
        x=_point(sol)
        if any(all((x&(r>>1)).bit_count()%2==(r&1) for r in ev) for ev in raw):
            raise AssertionError('Lifted point violates an original event.')
        out.update(status='SAT',reason=why,witness=x,observation_witness=y,seed_indices=list(seed))
        return out
    p=_base(K,clauses)
    if p is None:
        out.update(status='UNSAT',reason='boolean_2sat_relaxation_unsat');return out
    out['unique_closures_tested']=1
    if good(p):return success(p,(),'consistent_2sat_model')
    reach=[1<<i for i in range(K)];unit=0;conflicts=set()
    for c in clauses:
        tr=[(i,b^((p>>i)&1)) for i,b in c]
        if len(tr)==1:
            i,b=tr[0]
            if b!=1:raise AssertionError('Translation lost the zero model.')
            unit|=1<<i;continue
        (i,b),(j,d)=tr
        if b and d:conflicts.add((1<<i)|(1<<j))
        elif b:reach[i]|=1<<j
        elif d:reach[j]|=1<<i
        else:raise AssertionError('Translation lost the zero model.')
    for j in range(K):
        for i in range(K):
            if reach[i] & (1<<j):reach[i]|=reach[j]
    def viable(C):return not C&unit and all(C&e!=e for e in conflicts)
    # Unique minimal antichain of positive-implication SCCs; no exponential
    # set of visited closures needs to be stored across enumeration.
    reps={}
    for i,closure in enumerate(reach):
        if viable(closure):reps.setdefault(closure,i)
    eligible=list(reps.values());out['eligible_generators']=len(eligible)
    for d in range(1,min(k,len(eligible))+1):
        for seed in combinations(eligible,d):
            if max_subsets is not None and out['subsets_tested']>=max_subsets:
                out['reason']='subset_budget_exhausted';return out
            out['subsets_tested']+=1
            selected=sum(1<<i for i in seed)
            if any((reach[i]&selected)!=(1<<i) for i in seed):continue
            C=0
            for i in seed:C|=reach[i]
            if not viable(C):continue
            out['unique_closures_tested']+=1
            if good(p^C):return success(p^C,seed,'parity_feasible_implication_closure')
    out.update(status='UNSAT',reason='degree_bounded_closures_exhausted');return out
