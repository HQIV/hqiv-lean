import math
from collections import deque

from mpmath import mp

# ───── Arbitrary-precision floats (mpf) for angle / mask geometry ─────


def _set_precision_for_n(n: int) -> None:
    """
    Set mpmath decimal precision from |n|. Comparisons use δ ~ 1/√n and small
    differences vs π/(2k); scale dps with magnitude (capped for speed).
    """
    if n <= 1:
        mp.dps = 50
        return
    # bit_length ~ log2(n); δ gets tighter as n grows
    b = n.bit_length()
    mp.dps = max(50, min(400, b + 36))


# ───── 3D helper functions ─────
def get_representations_3d(N):
    reps = []
    max_c = int(math.sqrt(N)) + 2
    for x in range(0, max_c):
        for y in range(x, max_c):
            z2 = N - x*x - y*y
            if z2 >= y*y:
                z = int(math.sqrt(z2) + 0.5)
                if z*z == z2 and z >= y:
                    reps.append((x, y, z))
    return reps

def compute_pairwise_angles_3d(rep):
    coords = [abs(c) for c in rep]
    pairs = [(coords[i], coords[j]) for i in range(3) for j in range(i+1, 3)]
    out = []
    for a, b in pairs:
        if a == 0:
            out.append(mp.pi / 2)
        else:
            out.append(mp.atan2(b, a))
    return out


def is_stabilized_3d(rep, theta_k, delta):
    x,y,z = rep
    deltas = [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
    for dx,dy,dz in deltas:
        nx,ny,nz = x+dx, y+dy, z+dz
        nn = nx*nx + ny*ny + nz*nz
        if abs(nn - (x*x + y*y + z*z)) > 2: continue
        n_angles = compute_pairwise_angles_3d((nx, ny, nz))
        tol = delta * mp.mpf("1.2")
        if any(abs(na - theta_k) <= tol for na in n_angles):
            return True
    return False

# ───── 4D helper functions (unchanged) ─────
def get_representations_4d(N):
    reps = []
    max_c = int(math.sqrt(N)) + 2
    for w in range(0, max_c):
        for x in range(w, max_c):
            for y in range(x, max_c):
                z2 = N - w*w - x*x - y*y
                if z2 >= y*y:
                    z = int(math.sqrt(z2) + 0.5)
                    if z*z == z2 and z >= y:
                        reps.append((w, x, y, z))
    return reps

def compute_pairwise_angles_4d(rep):
    coords = [abs(c) for c in rep]
    pairs = [(coords[i], coords[j]) for i in range(4) for j in range(i + 1, 4)]
    out = []
    for a, b in pairs:
        if a == 0:
            out.append(mp.pi / 2)
        else:
            out.append(mp.atan2(b, a))
    return out


def is_stabilized_4d(rep, theta_k, delta):
    w,x,y,z = rep
    deltas = [(1,0,0,0),(-1,0,0,0),(0,1,0,0),(0,-1,0,0),(0,0,1,0),(0,0,-1,0),(0,0,0,1),(0,0,0,-1)]
    for dw,dx,dy,dz in deltas:
        nw,nx,ny,nz = w+dw, x+dx, y+dy, z+dz
        nn = nw*nw + nx*nx + ny*ny + nz*nz
        if abs(nn - (w*w + x*x + y*y + z*z)) > 2: continue
        n_angles = compute_pairwise_angles_4d((nw, nx, ny, nz))
        tol = delta * mp.mpf("1.2")
        if any(abs(na - theta_k) <= tol for na in n_angles):
            return True
    return False

def get_candidates_from_rep(rep, N):
    """Purely geometric candidates from the positive integer legs of a rep."""
    legs = [abs(c) for c in rep if c > 0]
    cands = set()
    for leg in legs:
        if leg > 1 and N % leg == 0:
            cands.add(leg)
    for i in range(len(legs)):
        for j in range(i+1, len(legs)):
            prod = legs[i] * legs[j]
            if prod > 1 and N % prod == 0:
                cands.add(prod)
    return list(cands)

# ───── Hybrid oracle ─────
def hybrid_factor(N):
    if N <= 1:
        return []
    factors = []
    pending = deque([N])
    while pending:
        current = pending.popleft()
        if current <= 1:
            continue
        # Trivial 2-peel first
        while current % 2 == 0:
            factors.append(2)
            current //= 2
        if current == 1:
            continue

        # Try 3D first (fast); mpf precision follows `current`
        _set_precision_for_n(current)
        c = mp.mpf(current)
        r = mp.sqrt(c)
        delta = 1 / r
        k_max = 2
        while k_max < c ** (1 / mp.mpf(k_max)):
            k_max += 1
        k_max = max(k_max - 1, 2)
        reps = get_representations_3d(current)
        peeled = False
        for rep in reps:
            angles = compute_pairwise_angles_3d(rep)
            for k in range(2, k_max + 1):
                theta_k = mp.pi / (2 * mp.mpf(k))
                for alpha in angles:
                    if abs(alpha - theta_k) <= delta:
                        if is_stabilized_3d(rep, theta_k, delta):
                            cands = get_candidates_from_rep(rep, current)
                            for cand in cands:
                                if 2 < cand < current and current % cand == 0:
                                    pending.append(cand)
                                    pending.append(current // cand)
                                    peeled = True
                                    break
                            if peeled: break
                if peeled: break
            if peeled: break

        if peeled:
            continue

        # 4D fallback — try every rep; extraction uses legs only (no angle mask)
        reps4 = get_representations_4d(current)
        peeled4 = False
        for rep in reps4:
            cands = get_candidates_from_rep(rep, current)
            for cand in cands:
                if 2 < cand < current and current % cand == 0:
                    pending.append(cand)
                    pending.append(current // cand)
                    peeled4 = True
                    break
            if peeled4:
                break

        if not peeled4:
            factors.append(current)

    return sorted(factors)


class HurwitzQuaternion:
    def __init__(self, a, b, c, d):
        # a,b,c,d are halves (multiply by 2 for integer arithmetic)
        self.a2 = a * 2
        self.b2 = b * 2
        self.c2 = c * 2
        self.d2 = d * 2

    def norm(self):
        return (self.a2**2 + self.b2**2 + self.c2**2 + self.d2**2) // 4

    def conjugate(self):
        return HurwitzQuaternion(self.a2/2, -self.b2/2, -self.c2/2, -self.d2/2)

    def __mul__(self, other):
        a1 = mp.mpf(self.a2) / 2
        b1 = mp.mpf(self.b2) / 2
        c1 = mp.mpf(self.c2) / 2
        d1 = mp.mpf(self.d2) / 2
        a2 = mp.mpf(other.a2) / 2
        b2 = mp.mpf(other.b2) / 2
        c2 = mp.mpf(other.c2) / 2
        d2 = mp.mpf(other.d2) / 2
        a = a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2
        b = a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2
        c = a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2
        d = a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2

        def rh(t):
            return float(mp.nint(2 * t) / 2)

        return HurwitzQuaternion(rh(a), rh(b), rh(c), rh(d))

    def __eq__(self, other):
        if not isinstance(other, HurwitzQuaternion):
            return NotImplemented
        return (
            round(self.a2) == round(other.a2)
            and round(self.b2) == round(other.b2)
            and round(self.c2) == round(other.c2)
            and round(self.d2) == round(other.d2)
        )

def is_hurwitz(q):
    """Check if all coefficients are integer or all half-integer with even sum."""
    return (q.a2 + q.b2 + q.c2 + q.d2) % 2 == 0

def hurwitz_divides(beta, alpha):
    """Return quotient if alpha divides beta, else None."""
    n = alpha.norm()
    if n == 0: return None
    gamma = beta * alpha.conjugate()
    if not is_hurwitz(gamma): return None
    q = HurwitzQuaternion(gamma.a2 // n, gamma.b2 // n, gamma.c2 // n, gamma.d2 // n)
    if q * alpha == beta:   # exact division
        return q
    return None


def get_hurwitz_from_rep(rep):
    w, x, y, z = rep
    q = HurwitzQuaternion(w, x, y, z)
    if not is_hurwitz(q):
        # multiply by unit (1+i+j+k)/2 to make it Hurwitz
        u = HurwitzQuaternion(0.5, 0.5, 0.5, 0.5)
        q = q * u
    return q

# Hybrid algebraic oracle
def hybrid_algebraic_factor(N):
    if N <= 1:
        return []
    factors = []
    pending = deque([N])
    while pending:
        current = pending.popleft()
        if current <= 1:
            continue
        # Trivial 2-peel
        while current % 2 == 0:
            factors.append(2)
            current //= 2
        if current == 1:
            continue

        # Same 3D angle / stabilization peel as hybrid_factor
        _set_precision_for_n(current)
        c = mp.mpf(current)
        r = mp.sqrt(c)
        delta = 1 / r
        k_max = 2
        while k_max < c ** (1 / mp.mpf(k_max)):
            k_max += 1
        k_max = max(k_max - 1, 2)
        reps = get_representations_3d(current)
        peeled = False
        for rep in reps:
            angles = compute_pairwise_angles_3d(rep)
            for k in range(2, k_max + 1):
                theta_k = mp.pi / (2 * mp.mpf(k))
                for alpha in angles:
                    if abs(alpha - theta_k) <= delta:
                        if is_stabilized_3d(rep, theta_k, delta):
                            cands = get_candidates_from_rep(rep, current)
                            for cand in cands:
                                if 2 < cand < current and current % cand == 0:
                                    pending.append(cand)
                                    pending.append(current // cand)
                                    peeled = True
                                    break
                            if peeled:
                                break
                if peeled:
                    break
            if peeled:
                break

        if peeled:
            continue

        # Algebraic 4D fallback using Hurwitz division
        reps4 = get_representations_4d(current)
        peeled4 = False
        for rep in reps4:
            q = get_hurwitz_from_rep(rep)
            # Try candidate divisors from legs (purely from the rep)
            legs = [abs(c) for c in rep if c > 0]
            for i in range(len(legs)):
                for j in range(i, len(legs)):
                    # construct possible small Hurwitz prime from two legs
                    a = legs[i]
                    b = legs[j]
                    alpha = HurwitzQuaternion(a, b, 0, 0)  # example in one plane
                    quotient = hurwitz_divides(q, alpha)
                    if quotient is not None:
                        d = alpha.norm()
                        if 2 < d < current and current % d == 0:
                            pending.append(d)
                            pending.append(current // d)
                            peeled4 = True
                            break
                if peeled4: break
            if peeled4: break

        # Same unconditional 4D leg peel as hybrid_factor
        if not peeled4:
            reps4 = get_representations_4d(current)
            for rep in reps4:
                cands = get_candidates_from_rep(rep, current)
                for cand in cands:
                    if 2 < cand < current and current % cand == 0:
                        pending.append(cand)
                        pending.append(current // cand)
                        peeled4 = True
                        break
                if peeled4:
                    break

        if not peeled4:
            factors.append(current)  # final prime remainder

    return sorted(factors)

if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(
        description="Hybrid 3D/4D lattice-angle factorization (heuristic; may leave composites)."
    )
    p.add_argument("N", type=int, nargs="?", default=143, help="integer (default: 143)")
    p.add_argument(
        "-a",
        "--algebraic",
        action="store_true",
        help="use Hurwitz 4D fallback instead of angle-only 4D peel",
    )
    args = p.parse_args()
    fn = hybrid_algebraic_factor if args.algebraic else hybrid_factor
    print(fn(args.N))