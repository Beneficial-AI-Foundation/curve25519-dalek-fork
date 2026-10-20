import re, sys
p = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
d = (-121665 * pow(121666, -1, p)) % p
a = p - 1
A = 486662
src = open('/mnt/projects/curve25519-dalek/curve25519-dalek/src/backend/serial/u64/constants.rs').read()

def limbs_to_nat(ls):
    return sum(l << (51*i) for i, l in enumerate(ls)) % p

def parse_points(block):
    pts = []
    for m in re.finditer(r'EdwardsPoint \{\s*X: FieldElement51::from_limbs\(\[([^\]]*)\]\),\s*Y: FieldElement51::from_limbs\(\[([^\]]*)\]\),\s*Z: FieldElement51::from_limbs\(\[([^\]]*)\]\),\s*T: FieldElement51::from_limbs\(\[([^\]]*)\]\)', block):
        X, Y, Z, T = [limbs_to_nat([int(x) for x in g.replace('\n',' ').split(',') if x.strip()]) for g in m.groups()]
        pts.append((X, Y, Z, T))
    return pts

bp_block = src[src.index('pub const ED25519_BASEPOINT_POINT'):src.index('pub const ED25519_BASEPOINT_128_POINT')]
BX, BY, BZ, BT = parse_points(bp_block)[0]
assert BZ == 1
tor_block = src[src.index('pub const EIGHT_TORSION_INNER_DOC_HIDDEN'):]
tors = parse_points(tor_block)[:8]

def on_curve(x, y):
    return (a*x*x + y*y - 1 - d*x*x*y*y) % p == 0

def add(P, Q):
    x1, y1 = P; x2, y2 = Q
    den = d*x1*x2*y1*y2 % p
    x3 = (x1*y2 + x2*y1) * pow(1+den, -1, p) % p
    y3 = (y1*y2 - a*x1*x2) * pow(1-den, -1, p) % p
    return (x3, y3)

def mul(n, P):
    R = (0, 1)
    Q = P
    while n:
        if n & 1: R = add(R, Q)
        Q = add(Q, Q); n >>= 1
    return R

print("basepoint x =", BX)
print("basepoint y =", BY)
print("basepoint T = x*y?", BT == BX*BY % p)
print("on curve:", on_curve(BX, BY))
print("y = 4/5:", BY == 4*pow(5, -1, p) % p)
print("x even:", BX % 2 == 0)
print("L*B = 0:", mul(L, (BX, BY)) == (0, 1))
T = (tors[1][0], tors[1][1])
print("torsion8 x =", T[0]); print("torsion8 y =", T[1])
print("torsion T on curve:", on_curve(*T), "T=xy:", tors[1][3] == T[0]*T[1] % p)
print("8T=0:", mul(8, T) == (0,1), "4T:", mul(4, T))
for i, pt in enumerate(tors):
    assert pt[2] == 1
    print(i, "dalek == i*T:", (pt[0], pt[1]) == mul(i, T), pt[0], pt[1])
# c with c^2 = -(A+2)
t = (-(A+2)) % p
# p = 5 mod 8: sqrt via x = t^((p+3)/8), adjust by sqrtM1
sqrtM1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752
c = pow(t, (p+3)//8, p)
if c*c % p != t:
    c = c * sqrtM1 % p
assert c*c % p == t
c = min(c, p - c)
print("c =", c, "c^2 = -486664:", c*c % p == (p - 486664))
print("2(a+d)/(a-d) == A:", 2*(a+d)*pow(a-d, -1, p) % p == A)
print("4/(a-d) =", 4*pow(a-d, -1, p) % p, "== c^2?", 4*pow(a-d, -1, p) % p == c*c % p)
print("d =", d)
# sqrtM1 even? for c choose smaller
print("p mod 8 =", p % 8)
print("2p < 16L:", 2*p < 16*L, " 8L <= 2p:", 8*L <= 2*p)
# Legendre of d
print("legendre d:", pow(d, (p-1)//2, p) == p-1)
# torsion8+basepoint
S = add(T, (BX, BY))
print("S x =", S[0], "y =", S[1])
