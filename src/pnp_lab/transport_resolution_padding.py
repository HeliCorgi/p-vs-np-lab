"""Private clause splits that preserve the Tseitin direct-transport antichain."""
from collections import Counter
from pnp_lab.transport_obstruction import switch_tseitin


def padded_tseitin(k, *, odd=True):
    n,cs=switch_tseitin(k,odd=odd)
    rows=[]
    for c in cs:
        if any(abs(l)<=k for l in c):
            rows.append(c)
        else:
            n+=1
            rows.extend(((*c[:-1],n),(-n,c[-1])))
    return n,tuple(rows)


def contract_twice(cs):
    """Unsigned occurrence degree two detects exactly these private helpers.

    This diagnostic is for generated inputs. Each reduced clause is obtained
    by an ordinary resolution, blindly to input IDs or signs of helpers.
    """
    occ=Counter(abs(l) for c in cs for l in c)
    helpers={v for v,count in occ.items() if count==2}
    halves={};result=[]
    for c in cs:
        hs=[l for l in c if abs(l) in helpers]
        if not hs:result.append(frozenset(c))
        elif len(hs)==1 and hs[0] not in halves:halves[hs[0]]=frozenset(l for l in c if l!=hs[0])
        else:raise ValueError("not independent split helpers")
    for w in helpers:result.append(halves[w]|halves[-w])
    return frozenset(result)
