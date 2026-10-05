"""Numeric check of Monge's theorem (three circles) + negative control.

External centre of similitude of circles i,j (centres O_i, O_j, radii r_i, r_j):
    S_ij = (r_i * O_j - r_j * O_i) / (r_i - r_j)
Theorem: S12, S23, S31 are collinear.
"""
import random, itertools
from fractions import Fraction as F

def sub(a, b): return (a[0]-b[0], a[1]-b[1])
def smul(s, a): return (s*a[0], s*a[1])
def ext(Oi, Oj, ri, rj): return smul(F(1)/(ri-rj), sub(smul(ri, Oj), smul(rj, Oi)))
def cross(u, v): return u[0]*v[1] - u[1]*v[0]

random.seed(1)
fails = 0
for _ in range(2000):
    O1 = (F(random.randint(-20,20)), F(random.randint(-20,20)))
    O2 = (F(random.randint(-20,20)), F(random.randint(-20,20)))
    O3 = (F(random.randint(-20,20)), F(random.randint(-20,20)))
    r1 = F(random.randint(1,10)); r2 = F(random.randint(1,10)); r3 = F(random.randint(1,10))
    if len({r1,r2,r3}) < 3: continue
    S12 = ext(O1,O2,r1,r2); S23 = ext(O2,O3,r2,r3); S31 = ext(O3,O1,r3,r1)
    if cross(sub(S23,S12), sub(S31,S12)) != 0:
        fails += 1
print("Monge collinearity failures (expect 0):", fails)

# negative control: arbitrary points on the three lines O1O2, O2O3, O3O1 are NOT collinear in general
neg = 0; tot = 0
for _ in range(2000):
    O1 = (F(random.randint(-20,20)), F(random.randint(-20,20)))
    O2 = (F(random.randint(-20,20)), F(random.randint(-20,20)))
    O3 = (F(random.randint(-20,20)), F(random.randint(-20,20)))
    def on(p,q):
        t = F(random.randint(-30,30), random.randint(1,7))
        return (p[0]+t*(q[0]-p[0]), p[1]+t*(q[1]-p[1]))
    A = on(O1,O2); B = on(O2,O3); C = on(O3,O1)
    tot += 1
    if cross(sub(B,A), sub(C,A)) == 0: neg += 1
print("negative-control collinear hits (expect small/0):", neg, "/", tot)

# non-vacuity concrete example
O1=(F(0),F(0)); O2=(F(4),F(0)); O3=(F(0),F(3)); r1=F(1); r2=F(2); r3=F(3)
S12=ext(O1,O2,r1,r2); S23=ext(O2,O3,r2,r3); S31=ext(O3,O1,r3,r1)
print("example S12,S23,S31:", S12, S23, S31, "cross=", cross(sub(S23,S12),sub(S31,S12)))
