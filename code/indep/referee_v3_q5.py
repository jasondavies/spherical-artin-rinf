# Exact arithmetic in Q(sqrt5): a + b*sqrt5 with Fractions. Referee's own code.
from fractions import Fraction as F

class Q5:
    __slots__ = ("a", "b")
    def __init__(self, a=0, b=0):
        self.a = F(a); self.b = F(b)
    def __add__(s, o):
        o = c5(o); return Q5(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __neg__(s): return Q5(-s.a, -s.b)
    def __sub__(s, o):
        o = c5(o); return Q5(s.a - o.a, s.b - o.b)
    def __rsub__(s, o): return c5(o) - s
    def __mul__(s, o):
        o = c5(o); return Q5(s.a*o.a + 5*s.b*o.b, s.a*o.b + s.b*o.a)
    __rmul__ = __mul__
    def conj(s): return Q5(s.a, -s.b)          # Galois conjugation sqrt5 -> -sqrt5
    def norm(s): return s.a*s.a - 5*s.b*s.b
    def inv(s):
        n = s.norm(); return Q5(s.a/n, -s.b/n)
    def __truediv__(s, o): return s * c5(o).inv()
    def __eq__(s, o):
        o = c5(o); return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def key(s): return (s.a, s.b)
    def __float__(s): return float(s.a) + float(s.b)*5**0.5
    def __repr__(s): return f"({s.a}+{s.b}r5)"
    def iszero(s): return s.a == 0 and s.b == 0
    def ispos(s):
        # sign of a + b sqrt5
        a, b = s.a, s.b
        if b == 0: return a > 0
        if a >= 0 and b >= 0: return True
        if a <= 0 and b <= 0: return False
        if a > 0: return a*a > 5*b*b
        return 5*b*b > a*a

def c5(x): return x if isinstance(x, Q5) else Q5(x)

PHI = Q5(F(1, 2), F(1, 2))      # golden ratio
PHIi = Q5(F(-1, 2), F(1, 2))    # 1/phi = phi - 1
assert PHI * PHIi == Q5(1)
