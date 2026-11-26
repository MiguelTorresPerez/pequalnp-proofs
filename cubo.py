# Standalone: column-local Res(+) SAT search for PHP, one cube.\n# Column-local Res(+) with semantic weakening: SAT search.
# Literal = (c, mask, b): equation  parity(mask & x_c) == b  over column c.
# Proof (oldest first): ('ax', R) | ('res', R, a, b, (c,mask)) [(f,False) in a, (f,True) in b] | ('weak', R, a)
import sys, pickle, time, itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

def par(x): return bin(x).count('1') & 1

def php(m, n):
    ax = []
    for i in range(m):
        ax.append(('pig', i, frozenset((j, 1 << i, True) for j in range(n))))
    for j in range(n):
        for a in range(m):
            for b in range(a + 1, m):
                ax.append(('hole', (a, b, j), frozenset([(j, 1 << a, False), (j, 1 << b, False)])))
    return [m] * n, ax

def bphp(m, nb):
    ax = []
    for i in range(m):
        for i2 in range(i + 1, m):
            for al in itertools.product([False, True], repeat=nb):
                ax.append(('bp', (i, i2, al), frozenset([(b, 1 << i, not al[b]) for b in range(nb)] +
                                                       [(b, 1 << i2, not al[b]) for b in range(nb)])))
    return [m] * nb, ax

def Fc(line, c, nc):
    # set of points of column c falsifying all col-c eqs of line
    eqs = [(mk, b) for (cc, mk, b) in line if cc == c]
    return frozenset(p for p in range(1 << nc) if all(par(mk & p) != b for (mk, b) in eqs))

def implies(C, D, cols):
    # C |= D ?
    Fs = [Fc(D, c, nc) for c, nc in enumerate(cols)]
    if any(not F for F in Fs): return True
    return all(Fs[c] <= Fc(C, c, nc) for c, nc in enumerate(cols))

def check(proof, cols, axset):
    for k, e in enumerate(proof):
        if e[0] == 'ax':
            assert e[1] in axset, e
        elif e[0] == 'res':
            _, R, a, b, f = e
            assert a < k and b < k
            C, D = proof[a][1], proof[b][1]
            fl, tl = (f[0], f[1], False), (f[0], f[1], True)
            assert fl in C and tl in D, e
            assert R == (C - {fl}) | (D - {tl})
        else:
            _, R, a = e
            assert a < k and implies(proof[a][1], R, cols), e
    assert frozenset() in [e[1] for e in proof]
    return len(proof)

def prune(proof):
    k0 = next(k for k, e in enumerate(proof) if e[1] == frozenset())
    need = set(); st = [k0]
    while st:
        k = st.pop()
        if k in need: continue
        need.add(k)
        e = proof[k]
        if e[0] == 'res': st += [e[2], e[3]]
        elif e[0] == 'weak': st.append(e[2])
    order = sorted(need); rm = {k: t for t, k in enumerate(order)}
    out = []
    for k in order:
        e = proof[k]
        if e[0] == 'ax': out.append(e)
        elif e[0] == 'res': out.append(('res', e[1], rm[e[2]], rm[e[3]], e[4]))
        else: out.append(('weak', e[1], rm[e[2]]))
    return out

class Enc:
    def __init__(self, cols, prefix, L, forms=None, maxw=None, outs=None, mustuse=True, noweak_after=None):
        # prefix: list of fixed lines (clauses); L derived lines. outs: if given, list of clauses that must
        # appear among derived lines (instead of empty last line).
        self.cols = cols
        self.pool = pool = IDPool(); cnf = self.cnf = []
        if forms is None:
            forms = [(c, mk) for c, nc in enumerate(cols) for mk in range(1, 1 << nc)]
        self.forms = forms
        lits = [(c, mk, b) for (c, mk) in forms for b in (False, True)]
        self.lits = lits
        A0 = len(prefix); self.A0 = A0; self.L = L; self.prefix = prefix
        T = A0 + L
        # literal true at point p in column c?
        litsc = {c: [l for l in lits if l[0] == c] for c in range(len(cols))}
        def X(t, l):
            if t < A0: return True if l in prefix[t] else False
            return pool.id(('x', t, l))
        self.X = X
        # z for fixed lines: constants
        zfix = {}
        for t in range(A0):
            for c, nc in enumerate(cols):
                F = Fc(prefix[t], c, nc)
                for p in range(1 << nc): zfix[(t, c, p)] = (p in F)
        def Z(t, c, p):
            if t < A0: return zfix[(t, c, p)]
            return pool.id(('z', t, c, p))
        for k in range(L):
            t = A0 + k
            K = pool.id(('K', t))
            As = [pool.id(('A', t, p)) for p in range(t)]
            Bs = [pool.id(('B', t, p)) for p in range(t)] + [pool.id(('Bn', t))]
            Vs = [pool.id(('V', t, f)) for f in forms] + [pool.id(('Vn', t))]
            for grp in (As, Bs, Vs):
                cnf.extend(CardEnc.equals(lits=grp, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses)
            cnf.append([K, pool.id(('Bn', t))]); cnf.append([-K, -pool.id(('Bn', t))])
            cnf.append([K, pool.id(('Vn', t))]); cnf.append([-K, -pool.id(('Vn', t))])
            if noweak_after is not None and k >= noweak_after:
                cnf.append([K])
            # cA, cB
            for l in lits:
                cA = pool.id(('cA', t, l)); cB = pool.id(('cB', t, l))
                for p in range(t):
                    a = As[p]; b = Bs[p]; lv = X(p, l)
                    if lv is True: cnf += [[-a, cA], [-b, cB]]
                    elif lv is False: cnf += [[-a, -cA], [-b, -cB]]
                    else: cnf += [[-a, -lv, cA], [-a, lv, -cA], [-b, -lv, cB], [-b, lv, -cB]]
                # if B is none, cB false
                cnf.append([-pool.id(('Bn', t)), -cB])
            for fi, f in enumerate(forms):
                V = Vs[fi]
                cnf.append([-V, pool.id(('cA', t, (f[0], f[1], False)))])
                cnf.append([-V, pool.id(('cB', t, (f[0], f[1], True)))])
            # resolvent definition (under K)
            for l in lits:
                x = X(t, l); cA = pool.id(('cA', t, l)); cB = pool.id(('cB', t, l))
                V = pool.id(('V', t, (l[0], l[1])))
                if not l[2]:  # (f,False): x <-> (cA & ~V) | cB
                    cnf += [[-K, -x, cA, cB], [-K, -x, -V, cB], [-K, -cA, V, x], [-K, -cB, x]]
                else:         # (f,True): x <-> cA | (cB & ~V)
                    cnf += [[-K, -x, cA, cB], [-K, -x, -V, cA], [-K, -cB, V, x], [-K, -cA, x]]
            # z definition
            for c, nc in enumerate(cols):
                for p in range(1 << nc):
                    z = Z(t, c, p)
                    tl = [X(t, l) for l in litsc[c] if par(l[1] & p) == l[2]]
                    for x in tl: cnf.append([-z, -x])
                    cnf.append([z] + tl)
                cnf.append([Z(t, c, p) for p in range(1 << nc)])  # non-tautological
            # weakening: ~K & A[p] & z[t,c,pt] -> z[p,c,pt]
            for p in range(t):
                a = As[p]
                for c, nc in enumerate(cols):
                    for pt in range(1 << nc):
                        zp = Z(p, c, pt)
                        if zp is True: continue
                        if zp is False: cnf.append([K, -a, -Z(t, c, pt)])
                        else: cnf.append([K, -a, -Z(t, c, pt), zp])
            if maxw is not None and k < L - 1:
                cnf.extend(CardEnc.atmost(lits=[X(t, l) for l in lits], bound=maxw, vpool=pool,
                                          encoding=EncType.seqcounter).clauses)
        if outs is None:
            last = T - 1
            for l in lits: cnf.append([-X(last, l)])
        else:
            for oi, o in enumerate(outs):
                sel = [pool.id(('O', oi, t)) for t in range(A0, T)]
                cnf.append(sel)
                for t, s in zip(range(A0, T), sel):
                    for l in lits:
                        cnf.append([-s, X(t, l)] if l in o else [-s, -X(t, l)])
        if mustuse:
            for t in range(A0, T - (1 if outs is None else 0)):
                users = []
                for t2 in range(t + 1, T):
                    users += [pool.id(('A', t2, t)), pool.id(('B', t2, t))]
                if outs is not None:
                    users += [pool.id(('O', oi, t)) for oi in range(len(outs))]
                cnf.append(users)

    def decode(self, model):
        ms = set(x for x in model if x > 0); pool = self.pool
        out = [('ax', c) for c in self.prefix]
        for k in range(self.L):
            t = self.A0 + k
            a = next(p for p in range(t) if pool.id(('A', t, p)) in ms)
            R = frozenset(l for l in self.lits if pool.id(('x', t, l)) in ms)
            if pool.id(('K', t)) in ms:
                b = next(p for p in range(t) if pool.id(('B', t, p)) in ms)
                f = next(f for f in self.forms if pool.id(('V', t, f)) in ms)
                out.append(('res', R, a, b, f))
            else:
                out.append(('weak', R, a))
        return out

def solve(enc, budget=None, solver='cadical153', extra=()):
    with Solver(name=solver, bootstrap_with=enc.cnf + list(extra)) as s:
        if budget:
            s.conf_budget(budget); r = s.solve_limited()
        else:
            r = s.solve()
        if r: return enc.decode(s.get_model())
        return r


# ---------------------------------------------------------------------------------------------
# cubo.py <L> <cube_id> <n_cubes> [m n] [solver]
# Length-L (derived lines) search for a column-local Res(+) refutation of PHP m->n (default 4->3),
# total lines = axioms + L. Symmetry breaking (pigeon x hole permutations): the final line is the
# empty clause obtained by resolving on the form  x_{0,0}+...+x_{w-1,0}  (column 0, first w pigeons).
# Cubes: n_cubes must be a multiple of m; cube c fixes w = c % m + 1 and the premise A of the final
# step to derived lines whose offset is = c // m (mod n_cubes // m).
# Prints SAT and the refutation (checked), or UNSAT. Needs only python3 + python-sat.
if __name__ == '__main__':
    L, cid, nc = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    m = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    n = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    solver = sys.argv[6] if len(sys.argv) > 6 else 'cadical153'
    assert nc % m == 0 and 0 <= cid < nc
    cols, ax = php(m, n)
    axcls = [c for (_, _, c) in ax]
    t0 = time.time()
    enc = Enc(cols, axcls, L)
    A0 = len(axcls); last = A0 + L - 1; pool = enc.pool
    w = cid % m + 1; k = nc // m; r = cid // m
    f = (0, (1 << w) - 1)
    extra = [[pool.id(('K', last))], [pool.id(('V', last, f))]]
    ok = [p for p in range(last) if p >= A0 and (p - A0) % k == r]
    extra.append([pool.id(('A', last, p)) for p in ok] if ok else [])
    if not ok:
        print('UNSAT (empty cube)'); sys.exit(0)
    print('cube', cid, 'of', nc, 'w', w, 'vars', pool.top, 'clauses', len(enc.cnf), flush=True)
    p = solve(enc, None, solver, extra)
    print('time', round(time.time() - t0, 1))
    if not p:
        print('UNSAT'); sys.exit(0)
    print('SAT total lines', check(p, cols, set(axcls)))
    pickle.dump(p, open('cubo_%d_%d_%d.pkl' % (L, cid, nc), 'wb'))
    for t, e in enumerate(p):
        print(t, e[0], e[2:] if len(e) > 2 else '', sorted(e[1]))
