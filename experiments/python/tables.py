import re, sys
p = 2**255 - 19
d = (-121665 * pow(121666, p-2, p)) % p
src = open('/mnt/projects/curve25519-dalek/curve25519-dalek/src/backend/serial/u64/constants.rs').read()
def section(start, end):
    i = src.index(start); j = src.index(end, i)
    return src[i:j]
def fes(text):
    out = []
    for m in re.finditer(r'from_limbs\(\[([^\]]*)\]\)', text):
        limbs = [int(x.strip().replace('_','')) for x in m.group(1).split(',') if x.strip()]
        out.append(limbs)
    return out
def val(l): return sum(x << (51*i) for i, x in enumerate(l))
By = 4 * pow(5, p-2, p) % p
def recover_x(y):
    u = (y*y - 1) % p; v = (d*y*y + 1) % p
    x2 = u * pow(v, p-2, p) % p
    x = pow(x2, (p+3)//8, p)
    if (x*x - x2) % p != 0:
        x = x * pow(2, (p-1)//4, p) % p
    if x % 2 == 1: x = p - x
    return x
Bx = recover_x(By)
def add(P, Q):
    x1,y1 = P; x2,y2 = Q
    t = d*x1*x2*y1*y2 % p
    x3 = (x1*y2 + y1*x2) * pow(1 + t, p-2, p) % p
    y3 = (y1*y2 + x1*x2) * pow(1 - t, p-2, p) % p
    return (x3, y3)
def mul(n, P):
    R = (0, 1); Q = P
    while n:
        if n & 1: R = add(R, Q)
        Q = add(Q, Q); n >>= 1
    return R
def check_an(entry, P):
    a, b, c = [val(l) for l in entry]
    x, y = P
    return a % p == (y + x) % p and b % p == (y - x) % p and c % p == 2*d*x*y % p
if __name__ == '__main__':
    t8 = fes(section('pub(crate) const AFFINE_ODD_MULTIPLES_OF_BASEPOINT:', 'pub(crate) const AFFINE_ODD_MULTIPLES_OF_BASEPOINT_128'))
    print(len(t8))
    ok = all(check_an(t8[3*k:3*k+3], mul(2*k+1, (Bx,By))) for k in range(64))
    print('naf8 ok', ok)
    bt = fes(section('static ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN', 'pub(crate) const AFFINE_ODD_MULTIPLES_OF_BASEPOINT:'))
    print(len(bt))
    ok = all(check_an(bt[3*(8*i+j):3*(8*i+j)+3], mul((j+1)*2**(8*i), (Bx,By))) for i in range(32) for j in range(8))
    print('table ok', ok)
    print('max val', max(val(l) for l in bt+t8) < p, max(max(l) for l in bt+t8) < 2**52)

def check_pn(entry, P):
    a, b, z, c = [val(l) for l in entry]
    x, y = P
    return z % p != 0 and a % p == z*(y + x) % p and b % p == z*(y - x) % p and c % p == 2*d*z*x*y % p
