"""Keep a list of raw 3-CNF restrictions; labels need preserve only SAT status.

Opaque labels are never branched on. Every retained representative is an
actual restricted source formula; an anchored disjunction is a temporary
label query only. Exhausting a width cap produces UNKNOWN, never a deletion.
"""
from .decision_labels import canonical_cnf, or_cnf, residual_label

YES, NO = ('YES',), ('NO',)


def _source(n, cs):
    if type(n) is not int or n<0 or isinstance(cs,(str,bytes)):
        raise ValueError('expected nonnegative scope and a signed 3-CNF')
    try:
        out=[]
        for c in cs:
            if isinstance(c,(str,bytes)):
                raise ValueError('clauses must be lists of signed integer literals')
            c=tuple(c)
            if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):
                raise ValueError('invalid clause width or literal')
            out.append(c)
    except TypeError as e:
        raise ValueError('expected a sequence of clauses') from e
    return canonical_cnf(n,out,3)


def _split(n,h,lit):
    return canonical_cnf(n,(tuple(l for l in c if l!=-lit) for c in h if lit not in c),3)


def _transport_layer(n, residuals, policy, stats):
    """Every deletion retains a target that is live at the time of deletion."""
    from .witness_transport import find_transport, check_transport
    cap,strategies,trace,derived=policy
    def moves(a,b):
        if cap is not None and stats['transport_checks']>=cap:
            stats['transport_budget_reached']=True
            return False
        stats['transport_checks']+=1
        cert=None
        if derived is None or derived['also_direct']:
            cert=find_transport(n,a,b,**({'strategies':strategies} if strategies is not None else {}))
            if cert is not None and not check_transport(n,a,b,cert):raise AssertionError('unverified witness transport')
        if cert is None and derived is not None:
            from .derived_transport import derive_transport,check_derived_transport
            from .interface_transport import find_interface_transport
            totals=stats['derivation']
            for finder in (find_interface_transport,derive_transport):
                totals['finder_calls']+=1
                def left(k):
                    return None if derived[k] is None else derived[k]-totals[k]
                r=finder(n,a,b,depth=derived['depth'],max_queries=left('queries'),max_nodes=left('nodes'))
                for key in ('queries','nodes','unit_steps','clause_scans','split_trials','candidate_maps'):
                    totals[key]+=r['stats'][key]
                totals['budget_limited'] |= r['stats']['budget_limited']
                cert=r['certificate']
                if cert is not None:
                    if not check_derived_transport(n,a,b,cert):raise AssertionError('unverified derived transport')
                    break
        if cert is None:return False
        stats['transport_drops']+=1
        hist=stats['transport_methods']
        hist[cert['method']]=hist.get(cert['method'],0)+1
        if trace is not None:trace.append(dict(source=a,target=b,certificate=cert))
        return True
    live=[]
    for current in residuals:
        j=0
        while j<len(live):
            if moves(current,live[j]):break
            if moves(live[j],current):live.pop(j)
            else:j+=1
        else:live.append(current)
    return live


def _layer(n, layer, mode, anchors, stats, policy=None):
    def key(h):
        stats['labels']+=1
        if not h:return YES
        if h==((),):return NO
        return residual_label(n,h,mode=mode)

    kept=[]
    seen=set()
    for h in layer:
        k=key(h)
        if k==YES:
            stats['individual_true']+=1
            return 'SAT', []
        if k==NO:
            stats['pruned_no']+=1
        elif k in seen:
            stats['individual_merges']+=1
        else:
            kept.append(h)
            seen.add(k)
    if not kept:return 'UNSAT', []
    if policy is not None and len(kept)>1:
        kept=_transport_layer(n,kept,policy,stats)
    if not anchors or len(kept)==1:return None,kept

    # One scan for each surviving anchor. Recheck membership on every
    # deletion, preserve earlier partners of this scan as live witnesses,
    # and abandon this scan if the anchor itself is proved UNSAT.
    live=dict(enumerate(kept))
    for i,anchor in enumerate(kept):
        if i not in live:continue
        partner_keys=set()
        for j,partner in list(live.items()):
            if i==j:continue
            stats['or_labels']+=1
            k=key(or_cnf(n,anchor,partner))
            if k==YES:
                stats['anchor_true']+=1
                return 'SAT', []
            if k==NO:
                del live[i],live[j]
                stats['anchor_false']+=1
                break
            if k in partner_keys:
                # If the anchor is SAT, it alone witnesses the list. If not,
                # the previous partner with this key has the same SAT bit.
                del live[j]
                stats['anchor_merges']+=1
            else:
                partner_keys.add(k)
    return (None,list(live.values())) if live else ('UNSAT',[])


def solve_pruned(n,clauses,*,order=None,max_width=64,label_mode='affine',anchor_collisions=True,
                 transport=False,transport_strategies=None,max_transport_checks=None,
                 transport_trace=False,split_parity=False,private_parity=False,
                 derived_depth=None,max_proof_nodes=None,max_proof_queries=None,recover_parity=False,case_parity=False,recover_case_parity=False):
    """Decide width-three SAT or return UNKNOWN at a retained-list width cap.

    Literals are signed one-based IDs. An explicit order must permute all
    zero-based variable indices. Absent variables need not be split. The cap
    is checked *after* each full pruning pass, including the root pass. It is
    not a bound on transient width or the time for a label computation.
    Set the cap to None for a complete decision algorithm. nodes counts all
    materialized individual restrictions at all levels; peak_width is before
    pruning, widths is after pruning (a decided level has no remaining list).
    stats.labels includes constant shortcuts and stats.or_labels is its OR
    request subset. The width cap does not bound a scan within a level.
    """
    if label_mode not in ('syntax','affine','blocked') or type(anchor_collisions) is not bool:
        raise ValueError('unknown label mode or nonboolean anchor option')
    if max_width is not None and (type(max_width) is not int or max_width<0):
        raise ValueError('expected nonnegative width cap or None')
    if any(type(b) is not bool for b in (transport,transport_trace,split_parity,private_parity,recover_parity,case_parity,recover_case_parity)):
        raise ValueError('expected Boolean method options')
    if max_transport_checks is not None and (type(max_transport_checks) is not int or max_transport_checks<0):
        raise ValueError('expected nonnegative transport check cap or None')
    if derived_depth is not None and (type(derived_depth) is not int or not 0<=derived_depth<=3):
        raise ValueError('derived depth must be 0,1,2,3')
    if any(v is not None and (type(v) is not int or v<0) for v in (max_proof_nodes,max_proof_queries)):
        raise ValueError('invalid derivation budget')
    if derived_depth is None and (max_proof_nodes is not None or max_proof_queries is not None):
        raise ValueError('proof budgets require derived_depth')
    if transport_strategies is not None and not transport:raise ValueError('strategies require direct transport')
    if not transport and derived_depth is None and (max_transport_checks is not None or transport_trace or transport_strategies is not None):
        raise ValueError('transport options require transport=True')
    if transport_strategies is not None:
        if isinstance(transport_strategies,(str,bytes)):raise ValueError('expected sequence of strategies')
        transport_strategies=tuple(transport_strategies)
        if any(v not in ('identity','flip','rename','single','constants') for v in transport_strategies):
            raise ValueError('unknown transport strategy')
    if sum((private_parity,split_parity,recover_parity,case_parity,recover_case_parity))>1:raise ValueError('select one root parity pass')
    # The optional root parity proof refers to the original caller's clause IDs.
    if any((split_parity,private_parity,recover_parity,case_parity,recover_case_parity)):
        if isinstance(clauses,(str,bytes)):raise ValueError('expected CNF')
        clauses=tuple(tuple(c) for c in clauses)
    source=_source(n,clauses)
    active={abs(l)-1 for c in source for l in c}
    if order is None:
        order=sorted(active)
    else:
        if isinstance(order,(str,bytes)):raise ValueError('expected variable order')
        try:order=tuple(order)
        except TypeError as e:raise ValueError('expected variable order') from e
        if (len(order)!=n or any(type(v) is not int or not 0<=v<n for v in order)
            or len(set(order))!=n):
            raise ValueError('order must permute zero-based variables')
        order=[v for v in order if v in active]
    stats=dict(labels=0,or_labels=0,pruned_no=0,individual_merges=0,individual_true=0,
               anchor_merges=0,anchor_true=0,anchor_false=0)
    trace=[] if transport_trace else None
    derived=(dict(depth=derived_depth,nodes=max_proof_nodes,queries=max_proof_queries,also_direct=transport)
             if derived_depth is not None else None)
    if derived is not None:stats['derivation']=dict(finder_calls=0,queries=0,nodes=0,unit_steps=0,
        clause_scans=0,split_trials=0,candidate_maps=0,budget_limited=False)
    policy=(max_transport_checks,transport_strategies,trace,derived) if transport or derived is not None else None
    if policy is not None:stats.update(transport_checks=0,transport_drops=0,transport_methods={},transport_budget_reached=False)
    parity_result=None
    layer=[source]; widths=[]; nodes=0; peak=0
    def answer(status):
        out=dict(status=status,nodes=nodes,widths=widths,peak_width=peak,
                    max_width=max_width,stats=stats,label_mode=label_mode,
                    anchor_collisions=anchor_collisions)
        if transport:out.update(transport=True,max_transport_checks=max_transport_checks)
        if derived is not None:out.update(derived_depth=derived_depth,max_proof_nodes=max_proof_nodes,
            max_proof_queries=max_proof_queries,max_transport_checks=max_transport_checks)
        if trace is not None:out['transport_trace']=trace
        if parity_result is not None:out['root_recovered_parity' if recover_parity or recover_case_parity else ('root_case_parity' if case_parity else ('root_private_parity' if private_parity else 'root_split_parity'))]=parity_result
        return out
    if any((split_parity,private_parity,recover_parity,case_parity,recover_case_parity)):
        if recover_parity or recover_case_parity:
            from .recovered_parity import recover_then_refute
            parity_result=recover_then_refute(n,clauses,case=recover_case_parity)
        elif case_parity:
            from .case_parity import case_parity_refute
            parity_result=case_parity_refute(n,clauses)
        elif private_parity:
            from .private_resolution import private_parity_refute
            parity_result=private_parity_refute(n,clauses)
        else:
            from .split_parity import split_parity_refute
            parity_result=split_parity_refute(n,clauses)
        if parity_result['status']=='UNSAT':return answer('UNSAT')
    for depth in range(len(order)+1):
        nodes+=len(layer);peak=max(peak,len(layer))
        status,layer=_layer(n,layer,label_mode,anchor_collisions,stats,policy)
        widths.append(len(layer))
        if status:return answer(status)
        if max_width is not None and len(layer)>max_width:return answer('UNKNOWN')
        if depth==len(order):
            raise AssertionError('fully restricted residual not decided')
        v=order[depth]+1
        layer=[_split(n,h,lit) for h in layer for lit in (-v,v)]
    raise AssertionError('unreachable')
