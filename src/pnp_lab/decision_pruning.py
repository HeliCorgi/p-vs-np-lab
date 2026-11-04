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


def _layer(n, layer, mode, anchors, stats):
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


def solve_pruned(n,clauses,*,order=None,max_width=64,label_mode='affine',anchor_collisions=True):
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
    layer=[source]; widths=[]; nodes=0; peak=0
    def answer(status):
        return dict(status=status,nodes=nodes,widths=widths,peak_width=peak,
                    max_width=max_width,stats=stats,label_mode=label_mode,
                    anchor_collisions=anchor_collisions)
    for depth in range(len(order)+1):
        nodes+=len(layer);peak=max(peak,len(layer))
        status,layer=_layer(n,layer,label_mode,anchor_collisions,stats)
        widths.append(len(layer))
        if status:return answer(status)
        if max_width is not None and len(layer)>max_width:return answer('UNKNOWN')
        if depth==len(order):
            raise AssertionError('fully restricted residual not decided')
        v=order[depth]+1
        layer=[_split(n,h,lit) for h in layer for lit in (-v,v)]
    raise AssertionError('unreachable')
