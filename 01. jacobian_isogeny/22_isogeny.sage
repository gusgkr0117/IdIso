class RichelotCorr:
    """
    The Richelot correspondance between hyperelliptic
    curves y²=g1*g2*g3 and y²=h1*h2*h3=hnew(x)

    It is defined by equations:
        g1(x1) h1(x2) + g2(x1) h2(x2) = 0
    and y1 y2 = g1(x1) h1(x2) (x1 - x2)

    Given a divisor D in Mumford coordinates:
        U(x) = x^2 + u1 x + u0 = 0
        y = V(x) = v1 x + v0
    Let xa and xb be the symbolic roots of U.
    Let s, p by the sum and product (s=-u1, p=u0)

    Then on x-coordinates, the image of D is defined by equation:
        (g1(xa) h1(x) + g2(xa) h2(x))
      * (g1(xb) h1(x) + g2(xb) h2(x))
    which is a symmetric function of xa and xb.
    This is a non-reduced polynomial of degree 4.

    Write gred = g-U = g1*x + g0
    then gred(xa) gred(xb) = g1^2*p + g1*g0*s + g0^2
    and  g1red(xa) g2red(xb) + g1red(xb) g2red(xa)
       = 2 g11 g21 p + (g11*g20+g10*g21) s + 2 g10*g20

    On y-coordinates, the image of D is defined by equations:
           V(xa) y = Gred1(xa) h1(x) (xa - x)
        OR V(xb) y = Gred1(xb) h1(x) (xb - x)
    If we multiply:
    * y^2 has coefficient V(xa)V(xb)
    * y has coefficient h1(x) * (V(xa) Gred1(xb) (x-xb) + V(xb) Gred1(xa) (x-xa))
      (x-degree 3)
    * 1 has coefficient Gred1(xa) Gred1(xb) h1(x)^2 (x-xa)(x-xb)
                      = Gred1(xa) Gred1(xb) h1(x)^2 U(x)
      (x-degree 4)
    """
    def __init__(self, G1, G2, H1, H2, hnew):
        assert G1[2].is_one() and G2[2].is_one()
        self.G1 = G1
        self.G2 = G2
        self.H1 = H1
        self.H11 = H1*H1
        self.H12 = H1*H2
        self.H22 = H2*H2
        self.hnew = hnew
        self.x = hnew.parent().gen()

    def map(self, D):
        "Computes (non-monic) Mumford coordinates for the image of D"
        U, V = D
        if not U[2].is_one():
            U = U / U[2]
        V = V  % U
        # Sum and product of (xa, xb)
        s, p = -U[1], U[0]
        # Compute X coordinates (non reduced, degree 4)
        g1red = self.G1 - U
        g2red = self.G2 - U
        assert g1red[2].is_zero() and g2red[2].is_zero()
        g11, g10 = g1red[1], g1red[0]
        g21, g20 = g2red[1], g2red[0]
        # see above
        Px = (g11*g11*p + g11*g10*s + g10*g10) * self.H11 \
           + (2*g11*g21*p + (g11*g20+g21*g10)*s + 2*g10*g20) * self.H12 \
           + (g21*g21*p + g21*g20*s + g20*g20) * self.H22

        # Compute Y coordinates (non reduced, degree 3)
        assert V[2].is_zero()
        v1, v0 = V[1], V[0]
        # coefficient of y^2 is V(xa)V(xb)
        Py2 = v1*v1*p + v1*v0*s + v0*v0
        # coefficient of y is h1(x) * (V(xa) Gred1(xb) (x-xb) + V(xb) Gred1(xa) (x-xa))
        # so we need to symmetrize:
        # V(xa) Gred1(xb) (x-xb)
        # = (v1*xa+v0)*(g11*xb+g10)*(x-xb)
        # = (v1*g11*p + v1*g10*xa + v0*g11*xb + v0*g10)*x
        # - xb*(v1*g11*p + v1*g10*xa + v0*g11*xb + v0*g10)
        # Symmetrizing xb^2 gives u1^2-2*u0
        Py1 = (2*v1*g11*p + v1*g10*s + v0*g11*s + 2*v0*g10)*self.x \
          - (v1*g11*s*p + 2*v1*g10*p + v0*g11*(s*s-2*p) + v0*g10*s)
        Py1 *= self.H1
        # coefficient of 1 is Gred1(xa) Gred1(xb) h1(x)^2 U(x)
        Py0 = self.H11 * U * (g11*g11*p + g11*g10*s + g10*g10)

        # Now reduce the divisor, and compute Cantor reduction.
        # Py2 * y^2 + Py1 * y + Py0 = 0
        # y = - (Py2 * hnew + Py0) / Py1
        _, Py1inv, _ = Py1.xgcd(Px)
        Py = (- Py1inv * (Py2 * self.hnew + Py0)) % Px
        assert Px.degree() == 4
        assert Py.degree() <= 3

        Dx = ((self.hnew - Py ** 2) // Px)
        Dy = (-Py) % Dx
        return (Dx, Dy)

def JacDbl(h, u, v):
    """
    Computes the double of a jacobian point (u,v)
    given by Mumford coordinates: except that u is not required
    to be monic, to avoid redundant reduction during repeated doubling
    """
    assert u.degree() == 2
    q, r = u.quo_rem(2*v)
    if r[0] == 0:
        a = q^2
        b = (v + (h - v^2)//v) % a
        return a, b
    else:
        h3 = 1 / (-r[0]) * q
        a = u^2
        b = (v + h3 * (h - v^2)) % a
        Dx = (h - b^2) // a
        Dy = (-b) % Dx
        return Dx, Dy

def JacDblIter(h, u, v, n):
    for _ in range(n):
        u, v = JacDbl(h, u, v)
    return u.monic(), v

def Gluing22(E1, E2, kernel, eval_points):
    K = E1.base()
    Rx.<x> = PolynomialRing(K)
    
    (P1, P2) = kernel[0]
    (Q1, Q2) = kernel[1]

    P12 = P1
    Q12 = Q1
    P22 = P2
    Q22 = Q2

    a1, a2, a3 = P12[0], Q12[0], (P12 + Q12)[0]
    b1, b2, b3 = P22[0], Q22[0], (P22 + Q22)[0]

    # Compute coefficients
    M = Matrix(K, [
        [a1*b1, a1, b1],
        [a2*b2, a2, b2],
        [a3*b3, a3, b3]])

    R, S, T = M.inverse() * vector(K, [1,1,1])
    RD = R * M.determinant()
    da = (a1 - a2)*(a2 - a3)*(a3 - a1)
    db = (b1 - b2)*(b2 - b3)*(b3 - b1)

    s1, t1 = - da / RD, db / RD
    s2, t2 = -T/R, -S/R

    a1_t = (a1 - s2) / s1
    a2_t = (a2 - s2) / s1
    a3_t = (a3 - s2) / s1
    h = s1 * (x**2 - a1_t) * (x**2 - a2_t) * (x**2 - a3_t)

    H = HyperellipticCurve(h)
    J = H.jacobian()

    def isogeny(pair):
        # Argument members may be None to indicate the zero point.

        # The projection maps are:
        # H->C: (xC = s1/x²+s2, yC = s1 y)
        # so we compute Mumford coordinates of the divisor f^-1(P_c): a(x), y-b(x)
        P, Q = pair
        if P:
            xP, yP = P.xy()
            JP = J([s1 * x**2 + s2 - xP, Rx(yP / s1)])
        # Same for E
        # H->E: (xE = t1 x² + t2, yE = t1 y/x^3)
        if Q:
            xQ, yQ = Q.xy()
            JQ = J([(xQ - t2) * x**2 - t1, yQ * x**3 / t1])
        if Q and P:
            return JQ + JP
        if Q:
            return JQ
        if P:
            return JP

    return H, [isogeny(D) for D in eval_points], isogeny

def Splitting22(J_kernel, eval_points):
    G1 = J_kernel[0][0]
    G2 = J_kernel[1][0]
    h = J_kernel[0].parent().curve().hyperelliptic_polynomials()[0]
    G3, r3 = h.quo_rem(G1*G2)
    assert r3 == 0
    delta = Matrix(G.padded_list(3) for G in (G1, G2, G3))
    assert delta.determinant() == 0

    """
    Construct the "split" isogeny from Jac(y^2 = G1*G2*G3)
    to a product of elliptic curves.

    This computation is the same as Benjamin Smith
    see 8.3 in http://iml.univ-mrs.fr/~kohel/phd/thesis_smith.pdf
    """
    h = G1*G2*G3
    R = h.parent()
    Fp2 = R.base()
    x = R.gen()

    M = Matrix(G.padded_list(3) for G in (G1,G2,G3))
    # Find homography
    u, v, w = M.right_kernel().gen()
    d = u/2
    (ad, _), (b, _) = (x**2 - v*x + w*d/2).roots()
    a = ad/d
    # Apply transform G(x) -> G((a*x+b)/(x+d))*(x+d)^2
    # The coefficients of x^2 are M * (1, a, a^2)
    # The coefficients of 1 are M * (d^2, b*d, b^2)
    H11, H21, H31 = M * vector([1, a, a*a])
    H10, H20, H30 = M * vector([d*d, b*d, b*b])
    assert G1((a*x+b)/(x+d))*(x+d)**2 == H11*x**2+H10

    h2 = (H11*x**2+H10)*(H21*x**2+H20)*(H31*x**2+H30)
    H2 = HyperellipticCurve(h2)
    p1 = (H11*x+H10)*(H21*x+H20)*(H31*x+H30)
    p2 = (H11+H10*x)*(H21+H20*x)*(H31+H30*x)
    # We will need to map to actual elliptic curve
    p1norm = (x + H10*H21*H31)*(x + H20*H11*H31)*(x + H30*H11*H21)
    p2norm = (x + H11*H20*H30)*(x + H21*H10*H30)*(x + H31*H10*H20)
    E1 = EllipticCurve(Fp, [0, p1norm[2], 0, p1norm[1], p1norm[0]])
    E2 = EllipticCurve(Fp, [0, p2norm[2], 0, p2norm[1], p2norm[0]])

    def morphE1(x, y):
        # from y^2=p1 to y^2=p1norm
        return (H11*H21*H31*x, H11*H21*H31*y)
    def morphE2(x, y):
        # from y^2=p1 to y^2=p2norm
        return (H10*H20*H30*x, H10*H20*H30*y)
    # The morphisms are:
    # inverse homography:
    # H->H2: x, y => ((b-dx) / (x-a), y/(x-a)^3)
    # then H2->E1:(x,y) => (x^2,y)
    #   or H2->E2:(x,y) => (1/x^2,y/x^3)
    def isogeny(D):
        HyperellipticCurve(h).jacobian()(D)
        # To map a divisor, perform the change of coordinates
        # on Mumford coordinates
        U, V = D
        # apply homography
        # y = v1 x + v0 =>
        U_ = U[0] * (x+d)**2 + U[1]*(a*x+b)*(x+d) + U[2]*(a*x+b)**2
        V_ = V[0] * (x+d)**3 + V[1]*(a*x+b)*(x+d)**2
        V_ = V_ % U_
        v1, v0 = V_[1], V_[0]
        # prepare symmetric functions
        s = - U_[1] / U_[2]
        p = U_[0] / U_[2]
        # compute Mumford coordinates on E1
        # Points x1, x2 map to x1^2, x2^2
        U1 = x**2 - (s*s - 2*p)*x + p**2
        # y = v1 x + v0 becomes (y - v0)^2 = v1^2 x^2
        # so 2v0 y-v0^2 = p1 - v1^2 xH^2 = p1 - v1^2 xE1
        if v0 == 0 :
            result1 = E1(0)
        else:
            V1 = (p1 - v1**2 * x + v0**2) / (2*v0)
            # Reduce Mumford coordinates to get a E1 point
            V1 = V1 % U1
            U1red = (p1 - V1**2) // U1
            if U1red[1] == 0 or V1 == 0: result1 = E1(0)
            else:
                xP1 = -U1red[0] / U1red[1]
                yP1 = V1(xP1)
                assert yP1**2 == p1(xP1)
                result1 = E1(morphE1(xP1, yP1))
        
        # Same for E2
        # Points x1, x2 map to 1/x1^2, 1/x2^2
        U2 = x**2 - (s*s-2*p)/p**2*x + 1/p**2
        # yE = y1/x1^3, xE = 1/x1^2
        # means yE = y1 x1 xE^2
        # (yE - y1 x1 xE^2)(yE - y2 x2 xE^2) = 0
        # p2 - yE (x1 y1 + x2 y2) xE^2 + (x1 y1 x2 y2 xE^4) = 0
        V21 = x**2 * (v1 * (s*s-2*p) + v0*s)
        V20 = p2 + x**4 * (p*(v1**2*p + v1*v0*s + v0**2))
        # V21 * y = V20
        _, V21inv, _ = V21.xgcd(U2)
        V2 = (V21inv * V20) % U2
        # assert V2**2 % U2 == p2 % U2
        # Reduce coordinates
        U2red = (p2 - V2**2) // U2
        if U2red == 0 or V2 == 0 : result2 = E2(0)
        else:
            xP2 = -U2red[0] / U2red[1]
            yP2 = V2(xP2)
            assert yP2**2 == p2(xP2)
            result2 = E2(morphE2(xP2, yP2))

        return result1, result2

    return (E1, E2), [isogeny((D[0], D[1])) for D in eval_points]

def FromJacToJac(h, D1, D2, a, powers, eval_points):
    R, x = h.parent().objgen()
    K = R.base()

    next_powers = None
    if not powers:
        if a >= 16:
            gap = ZZ(a).isqrt()
            _D1, _D2 = (D1[0], D1[1]), (D2[0], D2[1])
            doubles = [(0, _D1, _D2)]
            for i in range(a-1):
                _D1 = JacDbl(h, _D1[0], _D1[1])
                _D2 = JacDbl(h, _D2[0], _D2[1])
                doubles.append((i+1, _D1, _D2))
            _, (G1, _), (G2, _) = doubles[a-1]
            G1, G2 = G1.monic(), G2.monic()
            next_powers = [doubles[a-2*gap], doubles[a-gap]]
        else:
            G1, _ = JacDblIter(h, D1[0], D1[1], a-1)
            G2, _ = JacDblIter(h, D2[0], D2[1], a-1)
    else:
        (l, _D1, _D2) = powers[-1]
        if a >= 16: 
            next_powers = powers if l < a-1 else powers[:-1]
        G1, _ = JacDblIter(h, _D1[0], _D1[1], a-1-l)
        G2, _ = JacDblIter(h, _D2[0], _D2[1], a-1-l)
    
    G3, r3 = h.quo_rem(G1*G2)
    assert r3 == 0

    delta = Matrix(G.padded_list(3) for G in (G1, G2, G3))
    delta = delta.inverse()
    H1 = -delta[0][0]*x^2 + 2*delta[1][0]*x - delta[2][0]
    H2 = -delta[0][1]*x^2 + 2*delta[1][1]*x - delta[2][1]
    H3 = -delta[0][2]*x^2 + 2*delta[1][2]*x - delta[2][2]

    hnew = H1*H2*H3
    R = RichelotCorr(G1, G2, H1, H2, hnew)
    
    if a != 1:
        imD1 = R.map((D1[0], D1[1]))
        imD2 = R.map((D2[0], D2[1]))
    else:
        imD1 = [1, 0]
        imD2 = [1, 0]

    if next_powers:
        next_powers = [(l, R.map(_D1), R.map(_D2)) for l, _D1, _D2 in next_powers]
    
    eval_points = [R.map((D[0], D[1])) for D in eval_points]

    return hnew, (imD1[0], imD1[1]), (imD2[0], imD2[1]), next_powers, eval_points

def isogeny_22(J_kernel, eval_points, n):
    h = J_kernel[0].parent().curve().hyperelliptic_polynomials()[0]
    next_powers = None
    [D1, D2] = [(D[0], D[1]) for D in J_kernel]
    eval_points = [(D[0], D[1]) for D in eval_points]
    for i in range(n):
        h, D1, D2, next_powers, eval_points = FromJacToJac(h, D1, D2, n-i, next_powers, eval_points)
    
    J = HyperellipticCurve(h).jacobian()
    eval_points = [J([D[0], D[1]]) for D in eval_points]
    return J, eval_points