def JacDbl(Div):
    """
    Computes the double of a jacobian point (u,v)
    given by Mumford coordinates: except that u is not required
    to be monic, to avoid redundant reduction during repeated doubling
    """
    h = Div.parent().curve().hyperelliptic_polynomials()[0]
    u, v = Div[0], Div[1]
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

def JacMul(Div, n):
    J = Div.parent().curve().jacobian()
    tDiv = Div
    result = J(0)
    while n > 0 :
        if n % 2 == 1:
            result = result + tDiv
        tDiv = J(JacDbl(tDiv))
        n = n // 2
    return result

def JacToKummer(Div,F):
	#only implemented for the generic case
	f0,f1,f2,f3,f4,f5,f6 = F.coefficients(sparse=False)
	[A,B] = Div
	[a0,a1,a2] = A.monic().coefficients()
	[b0,b1] = B.coefficients()
	xi0 = 1
	xi1 = -a1
	xi2 = a0
	phi = 2*f0*xi0^3 + f1*xi0^2*xi1 + 2*f2*xi0^2*xi2 + f3*xi0*xi1*xi2 + 2*f4*xi0*xi2^2 + f5*xi1*xi2^2 + 2*f6*xi2^3
	y1y2 = b1^2*xi2 + b0*b1*xi1 + b0^2*xi0
	xi3 = (phi-2*y1y2)/(xi1^2-4*xi0*xi2)
	return [xi0,xi1,xi2,xi3]

def KummerToJac(Kum,F):
    Kx.<x> = PolynomialRing(Fp)
    f0,f1,f2,f3,f4,f5,f6 = F.coefficients(sparse=False)
    xi0, xi1, xi2, xi3 = Kum
    if xi0 == 0: return [1, 0]
    xi0, xi1, xi2, xi3 = 1, xi1/xi0, xi2/xi0, xi3/xi0
    phi = 2*f0*xi0^3 + f1*xi0^2*xi1 + 2*f2*xi0^2*xi2 + f3*xi0*xi1*xi2 + 2*f4*xi0*xi2^2 + f5*xi1*xi2^2 + 2*f6*xi2^3
    y1y2 = (phi - xi3 * (xi1^2-4*xi0*xi2)) / 2
    A = x^2 - xi1*x + xi2
    B = F % A
    y12py22 = 2 * B[0] + xi1 * B[1]
    y1py2 = sqrt(y12py22 + 2*y1y2)
    b12 = (y12py22 - 2*y1y2)/(xi1^2 - 4*xi2)
    b1 = sqrt(b12)
    b0 = (y1py2-(b1*xi1))/2

    if B != (b1*x + b0)^2 % A:
        b1 = -b1
        b0 = (y1py2-(b1*xi1))/2

    if B != (b1*x + b0)^2 % A:
        b1 = -b1
        y1py2 = -y1py2
        b0 = (y1py2-(b1*xi1))/2

    B = b1*x + b0

    return [A, -B]


def kernel_generators_from_message(message, B):
    T1 = B[0] + JacMul(B[2], message[0]) + JacMul(B[3], message[1])
    T2 = B[1] + JacMul(B[2], message[1]) + JacMul(B[3], message[2])
    return [T1, T2]

def get_cubic_Gx(D):
    assert((3*D).is_zero())
    Kab.<alpha, beta, lambda_> = PolynomialRing(Fp, 3)
    Kx.<x> = PolynomialRing(Kab)
    F = D.parent().curve().hyperelliptic_polynomials()[0]
    pol = F - (Kx(D[1]) + (alpha * x + beta) * Kx(D[0]))^2 - lambda_ * (Kx(D[0])^3)
    GB = ideal([pol[6], pol[5], pol[4], pol[3]]).groebner_basis()
    alpha = -GB[0].coefficients()[1]
    beta = -GB[1].coefficients()[1]
    Gx = D[1] + (alpha*x + beta)*D[0]
    return Gx

def get_rst_transform(Ti):
    Knew.<newr, news, newt, b, c, d, e, newtinv> = PolynomialRing(Fp, 8, order='degrevlex')
    Kx.<x> = PolynomialRing(Knew)

    T1, T2 = Ti[0], Ti[1]
    Gx1 = Kx(get_cubic_Gx(T1))
    Gx2 = Kx(get_cubic_Gx(T2))
    Hx1 = Kx(T1[0])
    Hx2 = Kx(T2[0])

    I0 = [newt*newtinv - 1]

    G1 = ((news - news*newt - 1)*x^3 + 3*news*(newr - newt)*x^2 + 3*news*newr*(newr - newt)*x - news*newt^2 + news*newr^3 + newt)
    Gx1eval = Kx((Gx1.subs(x=((x+b)/(c*x+d))) * (c*x+d)^3).numerator())
    I1 = [(e * G1[i] - Gx1eval[i]) for i in [0..3]]

    G2 = ((news - news*newt + 1)*x^3 + 3*news*(newr - newt)*x^2 + 3*news*newr*(newr - newt)*x - news*newt^2 + news*newr^3 - newt)
    Gx2eval = Kx((Gx2.subs(x=((x+b)/(c*x+d))) * (c*x+d)^3).numerator())
    I2 = [(e * G2[i] - Gx2eval[i]) for i in [0..3]]

    H1 = x^2 + newr*x + newt
    Hx1eval = Kx((Hx1.subs(x=((x+b)/(c*x+d))) * (c*x+d)^2).numerator())
    I3 = [((Hx1eval.leading_coefficient() * H1)[i] - Hx1eval[i]) for i in [0..1]]

    H2 = x^2 + x + newr
    Hx2eval = Kx((Hx2.subs(x=((x+b)/(c*x+d))) * (c*x+d)^2).numerator())
    I4 = [((Hx2eval.leading_coefficient() * H2)[i] - Hx2eval[i]) for i in [0..1]]

    I = Ideal(I0 + I1 + I2 + I4)
    GB = I.groebner_basis()

    r = -GB[0].coefficients()[1]
    s = -GB[1].coefficients()[1]
    t = -GB[2].coefficients()[1]

    a = 1
    b = -GB[3].coefficients()[1]
    c = -GB[4].coefficients()[1]
    d = -GB[5].coefficients()[1]
    e = -GB[6].coefficients()[1]
    return [r,s,t], [a,b,c,d,e]

def apply_transform(transform, points, f, rst):
    r,s,t = rst
    Kx.<x> = PolynomialRing(r.parent())
    f_rst = ((-s*t + s - 1)*x^3 + (-3*s*t + 3*s*r)*x^2 + (-3*s*t*r + 3*s*r^2)*x - s*t^2 + s*r^3 + t)^2 + 4*s*(x^2 + r*x + t)^3
    C = HyperellipticCurve(f_rst)
    J = C.jacobian()
    newK = KummerSurface(J)
    a, b, c, d, e = transform
    f0, f1, f2, f3, f4, f5, f6 = f.coefficients()
    ac = a * c
    bd = b * d
    abcd = ac * bd
    bcpad = b*c + a*d

    l0 = (-2) * (ac)^2 * (3*(bcpad)^2 - 8*abcd)*f0 + (2) * ac * (bcpad) * ((bcpad)^2 - 2*abcd)*f1 + (-4) * abcd * ((bcpad)^2 - 2*abcd) * f2 + bd * (bcpad)^3 * f3 + (-2) * (bd)^2  * (bcpad)^2* f4 + (4) * (bd)^3 * (bcpad) *f5 + (-8) * (bd)^4 *f6
    l2 = (-8) * (ac)^4 *f0 + (4) * (ac)^3 * (bcpad) *f1 + (-2) * (ac)^2 * (bcpad)^2 * f2 + ac * (bcpad)^3*f3 + (-4) * abcd * (b^2*c^2 + a^2*d^2) * f4 + (2) * bd * (bcpad) * (b^2*c^2 + a^2*d^2) * f5 + (-2) * (bd)^2 * (3*b^2*c^2 - 2*abcd + 3*a^2*d^2) * f6
    l1 = (-4) * (ac)^3 * (bcpad)*f0 + (ac)^2 * ((bcpad)^2 + 4*abcd) * f1 + (-4) * abcd*a*c * (bcpad)*f2 + abcd * ((bcpad)^2 + 4*abcd)*f3 + (-4) * ac * (bd)^2 * (bcpad)*f4 + (bd)^2 * ((bcpad)^2 + 4*abcd)* f5 + (-4) * (bd)^3 * (bcpad)*f6

    images = []
    for xx in points:
        y1 = xx[2]*c^2 + xx[1]*c*d + xx[0]*d^2
        y2 = 2*xx[2]*a*c + xx[1]*(bcpad) + 2*xx[0]*b*d
        y3 = xx[2]*a^2 + xx[1]*a*b + xx[0]*b^2
        y4 = e*((a*d-b*c)^4*xx[3] + l2*xx[2] + l1*xx[1] + l0*xx[0])
        images.append(newK([y1,y2,y3,y4]))
    return images

def get_codomain_curve_polynomial(rst):
    r,s,t = rst
    Kx.<x> = PolynomialRing(r.parent())

    e1 = s
    e2 = t
    e3 = r - 1
    e4 = r - t
    e5 = r*s - s*t - 1
    e6 = r^2 - t
    Delta = (e1*e3*e6)^2 + e5*(e3*e6*(e1*e4 + e5) + e4^2*e5)

    Gco = Delta*( (s - s*t - 1)*x^3 + 3*s*e4*x^2 + 3*r*s*e4*x + r^3*s - s*t^2 - t )
    Hco = e3*e5*x^2 + (r^3*s - 2*r^2*s + r*s*t + r - s*t^2 + s*t - t)*x - e5*e6
    lambdaco = 4*Delta*s*t

    Fco = Gco^2 + lambdaco*Hco^3
	
    return -3*Fco;

def get_codomain_Kummer_coefficients(rst):
	INV2 = Fp(1/2); INV3 = Fp(1/3); INV4 = Fp(1/4); INV16 = Fp(1/16); INV216 = Fp(1/216); INV864 = Fp(1/864);
	INV103680 = Fp(1/103680); INV213408 = Fp(1/213408); INV13837824 = Fp(1/13837824); INV8115344640 = Fp(1/8115344640); INV327019680 = Fp(1/327019680);
	r,s,t = rst
	e1 = s
	e2 = t
	e3 = r - 1
	e4 = r - t
	e5 = r*s - s*t - 1
	e6 = r^2 - t
	Delta = (e1*e3*e6)^2 + e5*(e3*e6*(e1*e4 + e5) + e4^2*e5)
	if Delta == 0: return Delta, 0, 0, 0, 0
	
	invD = 1/Delta

	j0fac = e1*( e1*( e1*( e6^2*( e6^2*(e4*e5 + e3) - e3*e4^2*(e3 + 1)) + (e2*e3*e4)^2*e4*e5) - e4*e5*(e2*e4^3 + e6^3)) + e2*(e2*Delta + e4^2*e5*(2*e5*e6 + e6)))
	j1fac = e1*( e1*( e6^3*( e5*(e1*e4^2 + e2 - 1) + e1*e3^2) + (e2*e3)^2*e3*e4*e5*(2 - e1*e4)) + e2*(Delta - e2*e3^3*e5))
	j2fac = e1*(e2*( Delta - (e3*e5)^2*e6*(2*e5 + 1)) + e1*e4^2*Delta )

	j0 = 36*Delta*j0fac
	j1 = 12*Delta*j1fac
	j2 = 36*Delta*j2fac

	Kx.<x> = PolynomialRing(r.parent())
	Hrst = x^2 + r*x + t
	Grst = (s - s*t - 1)*x^3 + 3*s*(r - t)*x^2 + 3*r*s*(r - t)*x + (r^3*s - s*t^2 + t)
	Frsti = (Delta*(Grst^2 + 4*s*Hrst^3)).coefficients()
	f0D = Frsti[0]; f1D = Frsti[1]; f2D = Frsti[2]; f3D = Frsti[3]; f4D = Frsti[4]; f5D = Frsti[5]; f6D = Frsti[6];
	Hrst_tilde = e3*e5*x^2 + (r^3*s - 2*r^2*s + r*s*t + r - s*t^2 + s*t - t)*x - e6*e5
	Grst_tilde = Grst - 2*t
	Frsti_tilde = (-3*(Delta*Grst_tilde^2 + 4*s*t*Hrst_tilde^3)).coefficients()
	h0 = Frsti_tilde[0]; h1 = Frsti_tilde[1]; h2 = Frsti_tilde[2]; h3 = Frsti_tilde[3]; h4 = Frsti_tilde[4]; h5 = Frsti_tilde[5]; h6 = Frsti_tilde[6];

	a0 = 0; a1 = 0; a2 = 0; a3 = Delta;
	b0 = 0; b1 = 0; b2 = Delta; b3 = 0;
	c0 = 0; c1 = Delta; c2 = 0; c3 = 0;
	a4 = f6D - h6
	c9 = f0D - h0
	a5 = (f5D - h5)*INV3
	b4 = -a5
	c8 = (f1D - h1)*INV3
	b9 = -c8
	b5 = 4*e1*( Delta*( 5*e2 - e1*e4^2 - 2*(e2*e3*e5 - e6)) + e2*(e3*e5)^2*e6*(12*e5 + 9) )
	a7 = 4*e1*(Delta*(e2 + e1*e4^2) - e2*(e3*e5)^2*e6*(3*e5 + 2))
	c4 = b5 + (f4D - h4)*INV3
	a6 = 2*b5 - c4 - 4*a7 + (f4D - h4)
	a8 = 12*e1* ( e1*( e6^3*( e5*(e4*e5 + e3) + e1*e3^2) - (e2*e3*e5)^2*e3*e4) + e2*(Delta + e2*e3*(e3*e5)^2))
	b7 = -4*e1* ( e2*( e5*( e3*e6*( e1*e3*e6*(-5*e5 - 4) - e4*e5^2) + 3*e4*Delta - 2*e4*(e4*e5)^2) - e2*Delta) + e1*e4^3*Delta)
	c5 = a8
	b6 = 4*(a8 - b7) - (f3D - h3)
	b8 = 4*e1*( Delta*( e1*( e6*( e6 -2*e4^2) - e2^2*(e3^2  - 5*e4)) + e2*(e6 - 5*e2*e5 + 2*e4)) - e2*e3*(e5*e6)^2*(12*e5 + 9))
	c7 = 4*e1* (Delta* ( e2*( e1*e4^2 + e6 + e2) + e1*e4^2*e6) + e2*e3*(e5*e6)^2*(2*e1*e4 + e5))
	a9 = b8 + (f2D - h2)*INV3
	c6 = 2*b8 - a9 - 4*c7 + (f2D - h2)
	
	a10 = (a4*b5 + f6D*(a6 - b5) - a5*(2*f5D + h5)*INV3 )*invD
	c19 = (c9*b8 + f0D*(c6 - b8) - c8*(2*f1D + h1)*INV3 )*invD
	a11 = (2*f6D*(b6 + 2*(c5 - b7)) + f5D*(a6 - a7 - c4) + 3*a4*b7 - h5*a7 )*invD
	c18 = (2*f0D*(b6 + 2*(a8 - b7)) + f1D*(c6 - c7 - a9) + 3*c9*b7 - h1*c7 )*invD
	b10 = (b4*c4 + 4*f6D*b7 - 4*h6*a8 + a7*(9*a5 + 4*h5) - 3*a4*(a8 + b7) )*invD*INV2
	b19 = (b9*a9 + 4*f0D*b7 - 4*h0*c5 + c7*(9*c8 + 4*h1) - 3*c9*(c5 + b7) )*invD*INV2
	a13 = (f6D*(10*a9 - 9*c6 - b8)*INV2 - h5*b7 - 3*b5*a7 + f5D*c5 )*invD
	c17 = (f0D*(10*c4 - 9*a6 - b5)*INV2 - h1*b7 - 3*b8*c7 + f1D*a8 )*invD
	b11 = (a4*(2*c7 - c6) + c4*(2*b5 - c4) + f6D*(4*b8 - 3*c6) + h6*(b8 - 2*a9) + 2*f5D*(a8 - b7) + a7*(2*a6 - a7) - 6*a13*Delta )*invD*INV4
	b18 = (c9*(2*a7 - a6) + a9*(2*b8 - a9) + f0D*(4*b5 - 3*a6) + h0*(b5 - 2*c4) + 2*f1D*(c5 - b7) + c7*(2*c6 - c7) - 6*c17*Delta )*invD*INV4
	a12 = (8*(2*f2D*a4 - a13*Delta + 12*h6*c7) + a5*(9*b6 - 7*f3D) - a5*(h3 - 32*a8) + 2*a7*(6*c4 - b5) - 2*a6*(2*c4 - 4*a6 + 11*a7) + 115*b6*(h6 - f6D + a4)*INV16 )*invD*INV16
	c15 = (8*(2*f4D*c9 - c17*Delta + 12*h0*a7) + c8*(9*b6 - 7*f3D) - c8*(h3 - 32*c5) + 2*c7*(6*a9 - b8) - 2*c6*(2*a9 - 4*c6 + 11*c7) + 115*b6*(h0 - f0D + c9)*INV16 )*invD*INV16
	c10 = (c7*(3*f6D + 5*h6 - a4) + c4^2 + 2*a5*a8 - a7*(2*a6 - a7) )*invD*INV4
	a19 = (a7*(3*f0D + 5*h0 - c9) + a9^2 + 2*c8*c5 - c7*(2*c6 - c7) )*invD*INV4
	a16 = (a7*(3*a8 + b7 - 2*f3D - b6) + c8*(3*f6D + h6) + a5*b8 - c7*(3*f5D + h5) + b5*a8 - a6*b7 )*invD*INV4
	c16 = (c7*(3*c5 + b7 - 2*f3D - b6) + a5*(3*f0D + h0) + c8*b5 - a7*(3*f1D + h1) + b8*c5 - c6*b7 )*invD*INV4
	b13 = (2*a7*(2*(f3D + b6) + h3 + a8 - b7) + 2*b5*(b7 + a8) - c4*(b7 + a8) - f5D*(3*a9 - 2*c6) + h5*(2*b8 - a9) - 4*f6D*c8 - 3*a5*c7 )*invD*INV4
	b17 = (2*c7*(2*(f3D + b6) + h3 + c5 - b7) + 2*b8*(b7 + c5) - a9*(b7 + c5) - f1D*(3*c4 - 2*a6) + h1*(2*b5 - c4) - 4*f0D*a5 - 3*c8*a7 )*invD*INV4
	a14 = (c8*(10*f6D - 3*a4) + b13*Delta - h5*(b8 + c6)*INV2 + f5D*(2*b8 - a9) - a7*(7*f3D - 6*a8) + 2*f4D*(a8 - b7) )*invD
	c14 = (a5*(10*f0D - 3*c9) + b17*Delta - h1*(b5 + a6)*INV2 + f1D*(2*b5 - c4) - c7*(7*f3D - 6*c5) + 2*f2D*(c5 - b7) )*invD
	c11 = (3*(c4*b7 + a7*a8)*INV2 - Delta*(2*b13 + 9*a16) + 4*(f5D*c7 - f6D*c8) )*invD
	a18 = (3*(a9*b7 + c7*c5)*INV2 - Delta*(2*b17 + 9*c16) + 4*(f1D*a7 - f0D*a5) )*invD
	b12 = ((b6*(c4 - a7) + a6*(a8 + b7))*INV2 + Delta*(b13 - a14 + 6*a16) - c4*b7 - a7*a8 )*invD
	b15 = ((b6*(a9 - c7) + c6*(c5 + b7))*INV2 + Delta*(b17 - c14 + 6*c16) - a9*b7 - c7*c5 )*invD
	b16 = (c7*(6*f4D + 2*h4 - a6 + a7) + 2*b5*(b8 - a9) + c9*(3*h6 - 7*f6D) + b7*(b7 - 2*b6) - 4*h0*a4 + a5*c8 - c6*a7 )*invD*INV4
	c13 = (c8*(a5 + 3*f5D + h5) - c9*(3*(h6 + a4) + 5*f6D) + b5*(b8 + 2*c7 - c6) + b7*(b7 - 2*b6) + a8^2 )*invD*INV4 - b16
	a17 = (a5*(c8 + 3*f1D + h1) - a4*(3*(h0 + c9) + 5*f0D) + b8*(b5 + 2*a7 - a6) + b7*(b7 - 2*b6) + c5^2 )*invD*INV4 - b16
	a15 = ((a6*(f2D - 5*c7  + b8 - h2) + a8*(a8 - b7 + 2*b6))*INV2 - a7*(5*f2D + 3*(c7 - b8) + h2)*INV3 + 2*c9*(3*f6D + h6) - (c8*(f5D + h5) - h1*a5) )*invD
	c12 = ((c6*(f4D - 5*a7  + b5 - h4) + c5*(c5 - b7 + 2*b6))*INV2 - c7*(5*f4D + 3*(a7 - b5) + h4)*INV3 + 2*a4*(3*f0D + h0) - (a5*(f1D + h1) - h5*c8) )*invD
	b14 = (2*(2*(f4D*c7 - f5D*c8 - f6D*c9) - h0*a4 - a5*c8 - f3D*b7 - c4*a9) - 3*h1*a5 + b8*(b5 + c4) + a8*(f3D + h3) )*invD + 4*(c13 - b16) + c12

	d0 = Delta^3
	d1 = Delta*j2
	d2 = Delta*j1
	d3 = Delta*j0
	d9 = Delta*( 2*(f0D*b5 - h4*c9) + c8*(f3D - 4*a8) + Delta*(4*c17 + c15) - j2fac*(108*c9 + 72*h0) + 4*f2D*c7)
	d4 = Delta*( 2*(f6D*b8 - h2*a4) + a5*(f3D - 4*c5) + Delta*(4*a13 + a12) - j0fac*(108*a4 + 72*h6) + 4*f4D*a7)
	d8 = Delta*( Delta*(4*c16 + c14) + b5*(h1 - f1D)*INV3 + 2*(f3D*c7 - 2*h0*a5 - f5D*c9))
	d5 = Delta*( Delta*(4*a16 + a14) + b8*(h5 - f5D)*INV3 + 2*(f3D*a7 - 2*h6*c8 - f1D*a4))
	d6 = Delta*( a8*(18144*c7 + 1344*(h2 - f2D) - 2016*b8  + 1386*h3 + 3198*f3D - 1770*b6)  + j0fac*(51840*h3 - 77760*b6 - 194400*b7 + 303264*c4 - 17712*b5 - 478656*f4D) + c6*(3888*b6 - 2592*h3 + 9720*b7 + 12528*f4D + 4644*b5 - 10584*c4) + b7*(6006*b6 - 678*h3 - 4890*f3D) + f1D*(1728*a6 - 8640*a7 - 1024*h5) + h1*(1296*a6 - 25920*j2fac - 22464*a5) + b6*(192*b6 + 384*f3D) + f2D*(4608*f4D - 512*h4) - f0D*(24384*h6 + 11904*f6D) + c8*(22768*h5 - 2416*f5D) - a9*(240*b5 + 1536*h4)+ 5664*b16*Delta + 49248*h0*a4 - 45600*h6*c9 - 1536*f3D^2 )*INV216
	d7 = Delta*( a8*(336*(f2D - h2) - 4536*c7 + 504*b8 - 822*f3D - 378*h3 + 474*b6) + j0fac*(19440*b6 - 12960*h3 + 48600*b7 - 71928*c4 + 119664*f4D + 3780*b5) + c6*(2646*c4 - 972*b6 + 648*h3 - 2430*b7 - 1161*b5 - 3132*f4D) + f3D*(384*f3D + 1299*b7 - 96*b6) + h1*(5616*a5 - 324*a6 + 6480*j2fac) + f1D*(256*h5 - 432*a6 + 2160*a7) + f0D*(2904*f6D + 6312*h6) + a9*(384*h4 - 12*b5) + f2D*(128*h4 - 1152*f4D) + b7*(165*h3 - 1461*b6) + c8*(592*f5D - 5680*h5) - 48*b6^2  - 1272*b16*Delta - 12312*h0*a4 + 11184*h6*c9)*INV216
	d10 = (a5*(f3D*(161280*c4 - 30720*f4D - 145920*a6 + 2343345*a7) + a5*(1488420*a9 - 3587400*b8 + 322560*f2D) - f4D*(30720*b6  + 199680*a8 + 284160*b7) + a7*(5539185*b6 + 691191*h3) + f5D*(510720*b8 - 7074540*c7) - 15360*f1D*h6 + 996480*b5*b7 + 10958040*a16*Delta  + 866880*c4*a8  + 1586340*h5*c7) + f5D*(f5D*(130560*b8 + 2453760*c7 - 215040*a9) + c4*(158400*b7 - 2588160*a8 - 11520*f3D) - a7*(680388*f3D + 2668740*b6 + 191292*h3) + f4D*(61440*a8 - 46080*b7) - 2780160*a16*Delta - 384000*b5*b7 + 7680*a6*b6 + 161280*f6D*c8) + a7*(h6*(69892224*a9- 131227776*c7- 33135744*c6 - 3661632*f2D) + c4*(4174608*b5 + 3304896*c4 - 2843904*f4D) + b5*(129696*b5 + 2325504*f4D) + f6D*(74365920*c7 - 13811968*f2D - 20964800*h2) - Delta*(2124480*a12 + 2182800*a13) + 34296960*a4*b8) + f6D*(a8*(552960*b6 - 2407680*b7 + 2313600*a8) + a6*(18504000*c7 - 46080*f2D + 568320*b8 + 9398400*a9) + c7*(35443200*h4 - 59031360*b5) + c4*(138240*f2D - 8559360*a9)) + c4*(a6*(15360*f4D + 81600*c4 - 76800*b5) + 2525760*h5*b7 - 184320*a12*Delta- 1411200*h6*b8  - 1558080*a4*c7) + h6*(b7*(1075200*f3D - 122880*b6 - 439680*b7) + 34560*a4*c9 - 15360*h3^2 - 764160*a6*c7) - a4*(a8*(608640*a8 - 2079360*b7) + 702720*a6*b8) + a6*Delta*(84480*a12 + 1265280*a13) )*INV103680 + (j0*a10 + j1*b10 + j2*c10)
	d11 = (a7*(f5D*(663936*f2D+ 331980*c7 + 2228928*a9 - 3106272*c6) + f3D*(1445873*a6 - 1920672*c4  - 881400*a7) + a5*(5212692*b8- 3170316*f2D - 2121108*h2) + a8*(2798016*f4D - 1217892*c4 + 74932*b5) + a6*(480831*h3  - 49647*b6) + b7*(3974724*c4- 3129984*f4D) - a7*(241176*b6 + 1537536*h3) - 165984*h1*a4  + 8144136*a16*Delta  + 4161756*h5*c7) + b7*(b5*(284544*h4- 480168*b5 + 441064*a6) + f5D*(160056*b7 - 35568*h3 + 326040*a8) + h5*(118560*h3 - 17784*b6 - 569088*b7) + a4*(480168*a9 - 960336*f2D) + a6*(102960*f4D - 400556*c4) + 47424*h2*h6 - 1421732*a5*a8) + a5*(a8*(158080*b6 + 670852*a8 + 98800*h3) + h4*(8208*f2D + 24624*a9 - 24624*c6) + a6*(372576*c7 - 3496*b8) - c8*(160056*f5D + 88920*h5) - 332424*b5*c6 + 213408*h6*c9) + a8*(h6*(397176*a9 - 219336*c6 - 136344*f2D) - Delta*(725192*a13 + 158080*a12) + a4*(201552*b8 + 21736*h2) - 148200*f6D*h2) + a6*(h6*(253344*f1D - 747136*c8) + Delta*(56992*a14 + 3320512*a16) - f5D*(39624*b8 + 499408*c7) + 196352*h1*a4) + f5D*(189696*h0*h6 + h1*(71136*h5 - 82992*f5D) - 2736*h2*h4) - h5*(195624*b5*b8 - 11856*h1*h5 - 2736*h2*h4) + a16*Delta*(1849536*f4D - 5975424*c4) + 640224*f1D*f6D*b5)*INV213408 + (j0*a11 + j1*b11 + j2*c11)
	d12 = (a7*(a8*(71688639263904*b6 - 47633590083456*h3  + 8226721831536*a8 + 150071629876272*b7) + f2D*(726002896320*b5 - 179138718720*h4 + 138945245672016*a6 + 3086073952448*a7) + a6*(53546718093024*b8 - 151947714850584*a9 + 325475748300312*c7) + h4*(52749740160*a9 - 29732886144*c6 + 588120892416*c7) + a7*(6586890862080*b8 - 4249353171776*h2 - 118179243959904*c7) + b7*(11182445707680*f3D - 2820326389920*b7) + h5*(20027432146176*c8 - 8088690876864*f1D) - b5*(224586788400*a9 + 111193712928*c6) - 14100621058368*f5D*c8 - 18611697184704*h1*a5) + a6*(a8*(6525676207557*h3 - 22601221319781*f3D - 10603550635821*b6 + 80301151266336*a8) + a6*(13243726386768*c6 - 14700419646732*a9 - 11815674624*f2D + 15956038353324*c7) + h4*(4508524800*a9 + 1596351744*c6 - 2344823770176*c7) + b5*(8408066073336*c6 - 24346033920*f2D - 4030968240*a9) + b7*(55566725760*f3D - 273511527120*b7) + h5*(14260256617152*f1D - 30843403202664*c8) - 12028028084280*a15*Delta + 12154510984824*f5D*c8 + 28183820804568*h1*a5) + a8*(h5*(26468641652544*c7 + 23504123448*f2D + 24429383784*a9 - 5375754349992*c6) + f5D*(108746474616*a9 - 83614417848*f2D - 131580175896*c6) + f4D*(14126711040*b6 + 871146327168*b7) + a8*(32077009590912*h4 - 72100886590512*b5) + c4*(27577143360*h3 - 1117106909568*b7) +31709957760*f3D*h4 - 116319939840*f1D*a4 + 66604982184*h2*a5) + b7*(a5*(458399616012*f2D - 4438398297996*a9 + 2342796395004*c6) + f5D*(26218297404*h2 - 424505659968*f2D) + h5*(322851453444*h2 - 256082141952*b8) + b7*(844880615280*b5 - 500669994240*h4) + 8115344640*h1*a4 + 12336736557600*a16*Delta) + a9*(f6D*(230723116416*c6 - 4057672320*a9 - 86563676160*f2D) - 37729916640*a4*c7) + c7*(26149443840*h5*b6 - 866538466560*h4*c4 + 731141831160*b5^2 + 37504321920*f2D*a4) + f5D*(b5*(53989584480*c8  - 13826142720*f1D) + 10369607040*f4D*c8 + 13525574400*f3D*c6) - c6*(106107356160*f2D*f6D + 24556431744*h6*b8) + h4*(1352557440*a15*Delta - 1352557440*a4*c9) + h1*(5184803520*c4*a5  - 2404546560*h3*h6) + 36519050880*a4*a19*Delta - 601136640*f0D*h5^2)*INV8115344640 + (j0*a12 + j1*b12 + j2*c12)
	d13 = (a6*(a8*(152377957017*f3D - 43858328553*h3 - 542547965232*a8 + 70926086673*b6) + a7*(1027033984428*a9 - 939329740800*f2D - 364246057056*b8 - 2221420681944*c7) + a6*(99362564352*a9 - 72671040*f2D - 89555386368*c6 - 110375191650*c7) + b5*(218013120*f2D - 56749284936*c6  + 235471860*a9) + h4*(16654460832*c7 - 290684160*a9 + 266460480*c6) + h5*(208629280080*c8 - 96846091680*f1D) + b7*(2716672608*b7 - 2100591792*f3D) + 49052952*a4*c9 + 81476094024*a15*Delta - 81917937036*f5D*c8 - 190688851080*h1*a5) + a7*(a8*(324608223888*h3 - 485859058776*b6 - 49610165904*a8 - 1024182914976*b7) + h4*(2131683840*f2D - 2241445536*c7- 1731993120*c6 - 654039360*a9) + a7*(35892961856*h2 - 55359277320*b8 - 22401676160*f2D + 792582864408*c7) + b5*(3475392804*a9 - 3804328944*f2D + 2869454808*c6) + b7*(23841196236*b7 - 75249410184*f3D) + c8*(93792832848*f5D - 134772145560*h5)+ 124109677224*h1*a5 + 55935056112*f1D*h5) + a8*(h5*(37133566470*c6 - 117723554*f2D - 1120252614*a9 - 176536537632*c7) + f5D*(2268786338*f2D + 2892135402*c6 - 4942122042*a9) + c4*(196817400*h3 + 5019607476*b7) + a8*(490324404960*b5 - 218074296960*h4) - f4D*(3527778384*b7 + 24223680*b6) - 133230240*f3D*h4  + 245264760*f1D*a4 - 450065382*h2*a5) + b7*(a5*(28009741032*a9 - 3964646088*f2D - 17342227656*c6) + h5*(1181516544*b8 - 1946519640*h2) + b7*(4266587520*h4 - 7199866440*b5) + f5D*(4678872120*f2D - 319673952*h2) + 370622304*h1*a4) + c7*(327019680*h5*b6 + 218013120*h4*c4 + a4*(2411681688*a9 - 1183058136*c6) - 183948570*b5^2) + f6D*c6*(4113978336*a9 - 544763232*c6 - 1177270848*f2D) + f5D*(436026240*f1D*b5 - 13625820*b5*c8 - 690374880*f4D*c8) + Delta*(218013120*h2*a13- 109006560*h4*a15 - 85899528000*b7*a16) + h1*(96894720*h3*h6 - 136258200*c4*a5) + 109006560*h4*a4*c9 + 290684160*f0D*h5^2 - 2943177120*f6D*a9^2) *INV327019680 + (j0*a13 + j1*b13 + j2*c13)
	d14 = (a7*(f3D*(1609023*c7 - 680238*a9 + 952359*c6 - 331056*f2D) + b6*(1197666*a9 - 335088*f2D - 3120369*c7 - 360885*c6) + f1D*(1352928*c4 - 1327680*b5 + 144384*f4D) + h3*(333360*f2D - 293499*c7 - 6489*b8) + c8*(1074888*c4 - 2640096*f4D + 30024*b5) + h5*(2385984*c9 - 932928*f0D)+ 357120*a18*Delta - 6584256*h0*a5 - 537168*f5D*c9) + b7*(b7*(378*b6 - 630*f3D - 42*h3) + b8*(87876*h4 - 61092*f4D - 148056*b5) + c7*(397776*c4 - 109248*b5 - 747360*f4D) + a9*(35136*f4D + 31704*c4) + a8*(1680*b6 + 3552*f3D) + c8*(78288*f5D - 228888*a5) + 2592*a4*c9 + 8640*a15*Delta - 27984*f1D*a5) + c7*(f5D*(1445940*c7 - 535440*b8 - 82176*f2D) + a6*(8448*f3D + 40272*b6) + a8*(161568*f4D - 125064*c4) - a5*(12684*a9 + 124128*f2D) - 7776*h6*c8  - 5935032*a16*Delta - 286332*h5*c7) + b8*(a8*(6300*c4 + 101844*b5 - 61920*f4D) + a5*(563760*a9 - 148686*c6 - 4032*f2D) + f5D*(44352*a9 - 195646*b8) - 108*a4*c8 + 151294*h5*b8) + a5*(2196*h0*a6 + c9*(2268*b5 - 864*f4D) - 3456*b6*c8 + 2880*f1D*h3 + a8*(159816*c8 - 72768*f1D) - 321216*a19*Delta) + Delta*(3456*c8*a12 + a16*(1410048*a9 - 902736*c6 + 176256*f2D) + 8064*a6*a18 - 2880*a8*a15) + a6*(f5D*(54356*f0D - 8496*h0) - 45860*f0D*h5) + c9*(3168*h6*a8 - 432*h3*a4)- 2880*f3D*a8^2)*INV864 + (j0*a14 + j1*b14 + j2*c14)
	d15 = (c7*(c5*(71688639263904*b6 - 47633590083456*h3  + 8226721831536*c5 + 150071629876272*b7) + f4D*(726002896320*b8 - 179138718720*h2 + 138945245672016*c6 + 3086073952448*c7) + c6*(53546718093024*b5 - 151947714850584*c4 + 325475748300312*a7) + h2*(52749740160*c4 - 29732886144*a6 + 588120892416*a7) + c7*(6586890862080*b5 - 4249353171776*h4 - 118179243959904*a7) + b7*(11182445707680*f3D - 2820326389920*b7) + h1*(20027432146176*a5 - 8088690876864*f5D) - b8*(224586788400*c4 + 111193712928*a6) - 14100621058368*f1D*a5 - 18611697184704*h5*c8) + c6*(c5*(6525676207557*h3 - 22601221319781*f3D - 10603550635821*b6 + 80301151266336*c5) + c6*(13243726386768*a6 - 14700419646732*c4 - 11815674624*f4D + 15956038353324*a7) + h2*(4508524800*c4 + 1596351744*a6 - 2344823770176*a7) + b8*(8408066073336*a6 - 24346033920*f4D - 4030968240*c4) + b7*(55566725760*f3D - 273511527120*b7) + h1*(14260256617152*f5D - 30843403202664*a5) - 12028028084280*c12*Delta + 12154510984824*f1D*a5 + 28183820804568*h5*c8) + c5*(h1*(26468641652544*a7 + 23504123448*f4D + 24429383784*c4 - 5375754349992*a6) + f1D*(108746474616*c4 - 83614417848*f4D - 131580175896*a6) + f2D*(14126711040*b6 + 871146327168*b7) + c5*(32077009590912*h2 - 72100886590512*b8) + a9*(27577143360*h3 - 1117106909568*b7) +31709957760*f3D*h2 - 116319939840*f5D*c9 + 66604982184*h4*c8) + b7*(c8*(458399616012*f4D - 4438398297996*c4 + 2342796395004*a6) + f1D*(26218297404*h4 - 424505659968*f4D) + h1*(322851453444*h4 - 256082141952*b5) + b7*(844880615280*b8 - 500669994240*h2) + 8115344640*h5*c9 + 12336736557600*c16*Delta) + c4*(f0D*(230723116416*a6 - 4057672320*c4 - 86563676160*f4D) - 37729916640*c9*a7) + a7*(26149443840*h1*b6 - 866538466560*h2*a9 + 731141831160*b8^2 + 37504321920*f4D*c9) + f1D*(b8*(53989584480*a5  - 13826142720*f5D) + 10369607040*f2D*a5 + 13525574400*f3D*a6) - a6*(106107356160*f4D*f0D + 24556431744*h0*b5) + h2*(1352557440*c12*Delta - 1352557440*c9*a4) + h5*(5184803520*a9*c8  - 2404546560*h3*h0) + 36519050880*c9*c10*Delta - 601136640*f6D*h1^2)*INV8115344640 + (j0*a15 + j1*b15 + j2*c15)
	d16 = (b7*(f4D*(28021592352*c7 - 1186872960*a9 - 90215424*f2D + 2564727256*b8) + b7*(11080992*h3 - 61233120*f3D + 36739872*b6) + c4*(15634944*f2D - 2143884288*a9 - 13429047840*c7) + f1D*(468525408*a5 - 31277376*f5D) + b8*(5647063032*b5  - 3255914584*h4) + c8*(8596985904*a5 - 2837594448*f5D) + a8*(18118464*f3D - 18670080*b6) + 4315057968*b5*c7 + 12224160*a15*Delta) + a7*(f3D*(10870942872*f2D - 49034471628*c7 + 21659664474*a9 - 31509056853*c6) + b6*(11004658584*f2D - 43666946766*a9 + 111387259092*c7 + 13921300635*c6) + f1D*(44079092448*b5 - 5433312768*f4D - 46842869568*c4) + h3*(187974099*b8 + 10704948264*c7 - 11120962200*f2D) + c8*(90357626208*f4D - 1937626536*b5 - 37449463512*c4) + c9*(24032217992*f5D - 86657028776*h5) + 237813785376*h0*a5  + 38797324800*f0D*h5 - 9889831872*a18*Delta) + b8*(f5D*(18592956792*c7- 1205128704*a9 - 12300288*f2D + 6491862111*b8) + a8*(1950122304*f4D + 192529896*c4 - 3659704464*b5) + a5*(59754240*f2D - 17589284478*a9 + 3699429813*c6) + a6*(8948160*b6 + 14092416*f3D) - 5222075775*h5*b8 ) + c7*(a5*(4309388928*f2D - 1812003696*a9) + f5D*(2948345088*f2D - 45120978720*c7) + a8*(4260518496*c4 - 5260253856*f4D) - a6*(346663200*f3D + 1408667520*b6) + 7915475520*h5*c7 + 211025095584*a16*Delta) + Delta*(a16*(35150202888*c6 - 5556385536*f2D - 56712723408*a9) + a19*(11345435712*a5 - 299120640*f5D) + 13837824*c9*a11 - 170775072*a6*a18 + 16320096*a8*a15 + 12300288*h2*a14) + h3*(h3*(3234816*b6 - 1078272*h3) - 741312*a4*c9 - 2426112*b6^2 + h4*(4313088*a9 - 1078272*c6 + 1437696*f2D)) + a6*(9424896*f4D*h1 + h0*(303996576*f5D - 58496256*a5) + f0D*(1627032160*h5 - 1976850304*f5D)) + b6*(h4*(1617408*c6 - 6469632*a9 - 2156544*f2D) + 5189184*a4*c9) + a8*(43041024*f3D*a8 + a5*(3190273008*f1D - 5827652064*c8)) + h1*h6*(18450432*a9 - 22843392*c6) - 8154432*f3D*a4*c9)*INV13837824 + (j0*a16 + j1*b16 + j2*c16)
	d17 = (c6*(c5*(152377957017*f3D - 43858328553*h3 - 542547965232*c5 + 70926086673*b6) + c7*(1027033984428*c4 - 939329740800*f4D - 364246057056*b5 - 2221420681944*a7) + c6*(99362564352*c4 - 72671040*f4D - 89555386368*a6 - 110375191650*a7) + b8*(218013120*f4D - 56749284936*a6  + 235471860*c4) + h2*(16654460832*a7 - 290684160*c4 + 266460480*a6) + h1*(208629280080*a5 - 96846091680*f5D) + b7*(2716672608*b7 - 2100591792*f3D) + 49052952*c9*a4 + 81476094024*c12*Delta - 81917937036*f1D*a5 - 190688851080*h5*c8) + c7*(c5*(324608223888*h3 - 485859058776*b6 - 49610165904*c5 - 1024182914976*b7) + h2*(2131683840*f4D - 2241445536*a7- 1731993120*a6 - 654039360*c4) + c7*(35892961856*h4 - 55359277320*b5 - 22401676160*f4D + 792582864408*a7) + b8*(3475392804*c4 - 3804328944*f4D + 2869454808*a6) + b7*(23841196236*b7 - 75249410184*f3D) + a5*(93792832848*f1D - 134772145560*h1)+ 124109677224*h5*c8 + 55935056112*f5D*h1) + c5*(h1*(37133566470*a6 - 117723554*f4D - 1120252614*c4 - 176536537632*a7) + f1D*(2268786338*f4D + 2892135402*a6 - 4942122042*c4) + a9*(196817400*h3 + 5019607476*b7) + c5*(490324404960*b8 - 218074296960*h2) - f2D*(3527778384*b7 + 24223680*b6) - 133230240*f3D*h2  + 245264760*f5D*c9 - 450065382*h4*c8) + b7*(c8*(28009741032*c4 - 3964646088*f4D - 17342227656*a6) + h1*(1181516544*b5 - 1946519640*h4) + b7*(4266587520*h2 - 7199866440*b8) + f1D*(4678872120*f4D - 319673952*h4) + 370622304*h5*c9) + a7*(327019680*h1*b6 + 218013120*h2*a9 + c9*(2411681688*c4 - 1183058136*a6) - 183948570*b8^2) + f0D*a6*(4113978336*c4 - 544763232*a6 - 1177270848*f4D) + f1D*(436026240*f5D*b8 - 13625820*b8*a5 - 690374880*f2D*a5) + Delta*(218013120*h4*c17- 109006560*h2*c12 - 85899528000*b7*c16) + h5*(96894720*h3*h0 - 136258200*a9*c8) + 109006560*h2*c9*a4 + 290684160*f6D*h1^2 - 2943177120*f0D*c4^2)*INV327019680 + (j0*a17 + j1*b17 + j2*c17)
	d18 = (c7*(f1D*(663936*f4D+ 331980*a7 + 2228928*c4 - 3106272*a6) + f3D*(1445873*c6 - 1920672*a9  - 881400*c7) + c8*(5212692*b5- 3170316*f4D - 2121108*h4) + c5*(2798016*f2D - 1217892*a9 + 74932*b8) + c6*(480831*h3  - 49647*b6) + b7*(3974724*a9- 3129984*f2D) - c7*(241176*b6 + 1537536*h3) - 165984*h5*c9  + 8144136*c16*Delta  + 4161756*h1*a7) + b7*(b8*(284544*h2- 480168*b8 + 441064*c6) + f1D*(160056*b7 - 35568*h3 + 326040*c5) + h1*(118560*h3 - 17784*b6 - 569088*b7) + c9*(480168*c4 - 960336*f4D) + c6*(102960*f2D - 400556*a9) + 47424*h4*h0 - 1421732*c8*c5) + c8*(c5*(158080*b6 + 670852*c5 + 98800*h3) + h2*(8208*f4D + 24624*c4 - 24624*a6) + c6*(372576*a7 - 3496*b5) - a5*(160056*f1D + 88920*h1) - 332424*b8*a6 + 213408*h0*a4) + c5*(h0*(397176*c4 - 219336*a6 - 136344*f4D) - Delta*(725192*c17 + 158080*c15) + c9*(201552*b5 + 21736*h4) - 148200*f0D*h4) + c6*(h0*(253344*f5D - 747136*a5) + Delta*(56992*c14 + 3320512*c16) - f1D*(39624*b5 + 499408*a7) + 196352*h5*c9) + f1D*(189696*h6*h0 + h5*(71136*h1 - 82992*f1D) - 2736*h4*h2) - h1*(195624*b8*b5 - 11856*h5*h1 - 2736*h4*h2) + c16*Delta*(1849536*f2D - 5975424*a9) + 640224*f5D*f0D*b8)*INV213408 + (j0*a18 + j1*b18 + j2*c18)
	d19 = (c8*(f3D*(161280*a9 - 30720*f2D - 145920*c6 + 2343345*c7) + c8*(1488420*c4 - 3587400*b5 + 322560*f4D) - f2D*(30720*b6  + 199680*c5 + 284160*b7) + c7*(5539185*b6 + 691191*h3) + f1D*(510720*b5 - 7074540*a7) - 15360*f5D*h0 + 996480*b8*b7 + 10958040*c16*Delta  + 866880*a9*c5  + 1586340*h1*a7) + f1D*(f1D*(130560*b5 + 2453760*a7 - 215040*c4) + a9*(158400*b7 - 2588160*c5 - 11520*f3D) - c7*(680388*f3D + 2668740*b6 + 191292*h3) + f2D*(61440*c5 - 46080*b7) - 2780160*c16*Delta - 384000*b8*b7 + 7680*c6*b6 + 161280*f0D*a5) + c7*(h0*(69892224*c4- 131227776*a7- 33135744*a6 - 3661632*f4D) + a9*(4174608*b8 + 3304896*a9 - 2843904*f2D) + b8*(129696*b8 + 2325504*f2D) + f0D*(74365920*a7 - 13811968*f4D - 20964800*h4) - Delta*(2124480*c15 + 2182800*c17) + 34296960*c9*b5) + f0D*(c5*(552960*b6 - 2407680*b7 + 2313600*c5) + c6*(18504000*a7 - 46080*f4D + 568320*b5 + 9398400*c4) + a7*(35443200*h2 - 59031360*b8) + a9*(138240*f4D - 8559360*c4)) + a9*(c6*(15360*f2D + 81600*a9 - 76800*b8) + 2525760*h1*b7 - 184320*c15*Delta- 1411200*h0*b5  - 1558080*c9*a7) + h0*(b7*(1075200*f3D - 122880*b6 - 439680*b7) + 34560*c9*a4 - 15360*h3^2 - 764160*c6*a7) - c9*(c5*(608640*c5 - 2079360*b7) + 702720*c6*b5) + c6*Delta*(84480*c15 + 1265280*c17) )*INV103680 + (j0*a19 + j1*b19 + j2*c19)

	ai = [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19]
	bi = [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19]
	ci = [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19]
	di = [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16,d17,d18,d19]

	return [ai,bi,ci,di], [j0,j1,j2,Delta^2]

def BFT_evaluation(kernel, points):
    J = kernel[0].parent()
    C = J.curve()
    f = C.hyperelliptic_polynomials()[0]
    rst, transform = get_rst_transform(kernel)
    a,b,c,d,e = transform
    transform_points = apply_transform([d,-b,-c,a,1/e^2], points, f, rst)
    fnew = get_codomain_curve_polynomial(rst)
    Cnew = HyperellipticCurve(fnew)
    Jnew = Cnew.jacobian()
    Knew = KummerSurface(Jnew)
    [ai, bi, ci, di], [_, _, _, _] = get_codomain_Kummer_coefficients(rst)
    codomain_points = []
    for pt in transform_points:
        k0, k1, k2, k3 = pt
        ki = [k3^3, k2*k3^2, k1*k3^2, k0*k3^2, k2^2*k3, k1*k2*k3, k0*k2*k3, k1^2*k3, k0*k1*k3, k0^2*k3, k2^3, k1*k2^2, k0*k2^2, k1^2*k2, k0*k1*k2, k0^2*k2, k1^3, k0*k1^2, k0^2*k1, k0^3]
        xi0 = sum([ai[j]*ki[j] for j in [0..len(ki)-1]])
        xi1 = sum([bi[j]*ki[j] for j in [0..len(ki)-1]])
        xi2 = sum([ci[j]*ki[j] for j in [0..len(ki)-1]])
        xi3 = sum([di[j]*ki[j] for j in [0..len(ki)-1]])
        codomain_points.append(Knew(xi0, xi1, xi2, xi3))

    return Jnew, codomain_points

def isogeny_33(J_kernel, eval_points, n):
    C = J_kernel[0].parent().curve()
    J = C.jacobian()
    func = C.hyperelliptic_polynomials()[0]
    kummer_surface = KummerSurface(J)
    pos = 0
    indices = [0]
    eval_length = len(eval_points)
    kernel_aux = [kummer_surface(JacToKummer(D, func)) for D in eval_points]
    kernel_aux = kernel_aux + [kummer_surface(JacToKummer(D, func)) for D in J_kernel]
    for i in [0..n-1]:
        kummer_surface = KummerSurface(J)
        func = J.curve().hyperelliptic_polynomials()[0]
        gap = n-i-1 - indices[pos]
        if gap == 0:
            kernel2 = [J(KummerToJac(D, func)) for D in kernel_aux[eval_length + 2*pos: eval_length + 2*pos+2]]
            if indices[pos] != 0:
                indices = indices[:-1]
                kernel_aux = kernel_aux[:-2]
                pos = pos - 1
        elif gap == 1:
            kernel2 = [3*J(KummerToJac(D, func)) for D in kernel_aux[eval_length + 2*pos: eval_length + 2*pos+2]]
            if indices[pos] != 0:
                indices = indices[:-1]
                kernel_aux = kernel_aux[:-2]
                pos = pos - 1
        else:
            new_ind = indices[pos] + floor(gap/2)
            new_aux = [JacMul(J(KummerToJac(D, func)), 3^floor(gap/2)) for D in kernel_aux[eval_length + 2*pos:eval_length + 2*pos+2]]
            indices.append(new_ind)
            kernel_aux = kernel_aux + [kummer_surface(JacToKummer(D, func)) for D in new_aux]
            pos = pos + 1
            new_aux = [JacMul(D, 3^ceil(gap/2)) for D in new_aux]
            kernel2 = new_aux
        J, kernel_aux = BFT_evaluation(kernel2, kernel_aux)
    func = J.curve().hyperelliptic_polynomials()[0]
    return J, [J(KummerToJac(D, func)) for D in kernel_aux[:eval_length]]

def hash_new(message, B):
    J = B[0].parent().curve().jacobian()
    kernel = kernel_generators_from_message(message, B)
    func = C.hyperelliptic_polynomials()[0]
    kummer_surface = KummerSurface(J)
    n = 80
    pos = 0
    indices = [0]
    kernel_aux = [kummer_surface(JacToKummer(D, func)) for D in kernel]
    for i in [0..n-1]:
        kummer_surface = KummerSurface(J)
        func = J.curve().hyperelliptic_polynomials()[0]
        gap = n-i-1 - indices[pos]
        if gap == 0:
            kernel2 = [J(KummerToJac(D, func)) for D in kernel_aux[2*pos:2*pos+2]]
            if indices[pos] != 0:
                indices = indices[:-1]
                kernel_aux = kernel_aux[:-2]
                pos = pos - 1
        elif gap == 1:
            kernel2 = [3*J(KummerToJac(D, func)) for D in kernel_aux[2*pos:2*pos+2]]
            if indices[pos] != 0:
                indices = indices[:-1]
                kernel_aux = kernel_aux[:-2]
                pos = pos - 1
        else:
            new_ind = indices[pos] + floor(gap/2)
            new_aux = [JacMul(J(KummerToJac(D, func)), 3^floor(gap/2)) for D in kernel_aux[2*pos:2*pos+2]]
            indices.append(new_ind)
            kernel_aux = kernel_aux + [kummer_surface(JacToKummer(D, func)) for D in new_aux]
            pos = pos + 1
            new_aux = [JacMul(D, 3^ceil(gap/2)) for D in new_aux]
            kernel2 = new_aux
        J, kernel_aux = BFT_evaluation(kernel2, kernel_aux)
        print("#" + str(i))
    return J.curve().igusa_clebsch_invariants()

