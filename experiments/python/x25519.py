p = 2**255 - 19
a24 = 121665
def clamp(k): return 2**254 + 8 * (k % 2**254 // 8)
def ladder(bits, k, u):
    x1 = u; x2, z2, x3, z3, swap = 1, 0, u, 1, 0
    for t in range(bits-1, -1, -1):
        kt = (k >> t) & 1
        swap ^= kt
        if swap: x2, x3 = x3, x2; z2, z3 = z3, z2
        swap = kt
        A = (x2+z2)%p; AA = A*A%p; B = (x2-z2)%p; BB = B*B%p; E = (AA-BB)%p
        C = (x3+z3)%p; D = (x3-z3)%p; DA = D*A%p; CB = C*B%p
        x3 = (DA+CB)**2 % p; z3 = x1*(DA-CB)**2 % p
        x2 = AA*BB % p; z2 = E*(AA + a24*E) % p
    if swap: x2, x3 = x3, x2; z2, z3 = z3, z2
    return x2 * pow(z2, p-2, p) % p
def x25519(k, u): return ladder(255, clamp(k), u % 2**255)
def le(h): return int.from_bytes(bytes.fromhex(h),'little')
k1=le('a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4'); u1=le('e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c')
print(clamp(k1)); print(x25519(k1,u1), le('c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552'))
k2=le('4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d'); u2=le('e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493')
print(x25519(k2,u2), le('95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957'))
ka=le('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a'); print(x25519(ka,9), le('8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a'))
# small model test: ZMod 1009, A=2 (A^2=4 bad) -> pick A=3? need A^2 != 4 and point. B=1
q=1009; A=3
def rhs(u): return (u**3+A*u*u+u)%q
pts=[(u,v) for u in range(q) for v in range(q) if (v*v-rhs(u))%q==0]
print(len(pts)+1, pts[:5])
