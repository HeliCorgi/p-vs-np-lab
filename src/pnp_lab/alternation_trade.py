"""Exact exponent replay for a *restricted*, published SAT lower-bound calculus.

There is no SAT solver or simulator here. The trusted mathematical rules and
their hypotheses are in docs/alternation_trade.md. All numbers are exact.
"""
from dataclasses import dataclass
from fractions import Fraction


MODEL = 'deterministic-random-access'
SPACE = 'n^o(1)'
ONE = Fraction(1)
ZERO = Fraction(0)


def _q(value):
    if type(value) not in (int, str, Fraction):
        raise ValueError('expected an integer, fraction, or rational string; no floats')
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('invalid rational number') from exc


@dataclass(frozen=True)
class Block:
    quantifier: str
    guess: Fraction
    passed: Fraction  # size exponent of the input passed on by this block


@dataclass(frozen=True)
class Line:
    blocks: tuple[Block, ...]
    time: Fraction

    def as_json(self):
        return dict(blocks=[dict(q=b.quantifier, guess=str(b.guess), passed=str(b.passed))
                            for b in self.blocks], time=str(self.time))


def replay(c, start, steps, *, model=MODEL, space=SPACE):
    """Replay only Williams rules Speedup 0, Speedup 1 and Slowdown.

    A speedup step is ('up', x); a slowdown is ('down',). The first
    quantifier defaults to existential, the rest alternate. A well-formed
    but noncontracting trace returns strict_contradiction=False.
    """
    if model != MODEL or space != SPACE:
        raise ValueError('these rules are only for deterministic random access and n^o(1) space')
    c, start = _q(c), _q(start)
    if c <= 1 or start < 1:
        raise ValueError('need c>1 and initial time exponent >=1')
    steps = tuple(steps)
    if not steps:
        raise ValueError('empty proof')
    lines = [Line((), start)]
    for i, step in enumerate(steps):
        blocks, t = lines[-1].blocks, lines[-1].time
        if not isinstance(step, (tuple, list)) or not step:
            raise ValueError('invalid instruction')
        if step[0] == 'up' and len(step) == 2:
            x = _q(step[1])
            if not (0 < x <= t-1):
                raise ValueError('need positive split and at least linear residual time')
            if not blocks:
                new = (Block('exists', x, max(ONE,x)), Block('forall',ZERO,ONE))
            else:
                b = blocks[-1]
                new = blocks[:-1] + (
                    Block(b.quantifier, max(b.guess,x), max(b.passed,x)),
                    Block('exists' if b.quantifier=='forall' else 'forall', ZERO, b.passed))
            lines.append(Line(new,t-x))
        elif tuple(step) == ('down',):
            if not blocks:
                raise ValueError('cannot discharge a nonexistent quantifier')
            b = blocks[-1]
            prev = blocks[-2].passed if len(blocks)>1 else ONE
            lines.append(Line(blocks[:-1], c*max(t,b.guess,b.passed,prev)))
        else:
            raise ValueError('unrecognized rule or wrong arity')
        if not lines[-1].blocks and i != len(steps)-1:
            raise ValueError('interior deterministic line is not in normal form')
    if lines[-1].blocks:
        raise ValueError('proof must end at a deterministic line')
    final = lines[-1].time
    return dict(model=model, space=space, c=str(c), lines=[l.as_json() for l in lines],
                strict_gap=str(start-final), strict_contradiction=final<start)


def standard_trace(c, *, template='seven'):
    """Two literature calibration templates. No search or optimality claim."""
    c = _q(c)
    if template == 'three':
        return replay(c,2,[('up',1),('down',),('down',)])
    if template != 'seven':
        raise ValueError('unknown template')
    x = c*c/2
    return replay(c,2+x,[('up',x),('up',1),('down',),('down',),('up',x),('down',),('down',)])


def checkpoint_envelope(a, s):
    """Optimize max(1,x+s,a-x), the explicit snapshot accounting envelope.

    Diagnostic only: does not license a trading rule for unrestricted space.
    """
    a, s = _q(a), _q(s)
    if not (a >= 1 and 0 <= s <= a):
        raise ValueError('need a>=1 and 0<=s<=a')
    x = (a-s)/2
    return dict(split=str(x), envelope=str(max(ONE,x+s,a-x)))
