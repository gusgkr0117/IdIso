from dataclasses import dataclass

from sage.algebras.quatalg.quaternion_algebra import basis_for_quaternion_lattice
from sage.algebras.quatalg.quaternion_algebra_element import QuaternionAlgebraElement_rational_field as QuaternionAlgebraElement
from sage.algebras.quatalg.quaternion_algebra import QuaternionFractionalIdeal_rational as QuaternionAlgebraIdeal
from sage.schemes.elliptic_curves.ell_point import EllipticCurvePoint_finite_field as EllipticCurvePoint
from sage.schemes.elliptic_curves.ell_finite_field import EllipticCurve_finite_field as EllipticCurve

from sage.rings.finite_rings.element_pari_ffelt import FiniteFieldElement_pari_ffelt as FiniteFieldElement
from sage.rings.integer import Integer

def get_basis(E: EllipticCurve, N: Integer):
    assert (prime^2 - 1) % N == 0
    P, Q = E(0), E(0)
    factors = N.factor()
    while True:
        P = E.random_point() * ((prime^2-1)//N)
        check = True
        for i in range(len(factors)):
            if ((N // factors[i][0]) * P).is_zero():
                check = False
                break
        if check : break
    
    while True:
        Q = E.random_point() * ((prime^2-1)//N)
        check = True
        for i in range(len(factors)):
            if ((N // factors[i][0]) * Q).is_zero():
                check = False
                break
        if not check : continue
        for i in range(len(factors)):
            cofactor = N // (factors[i][0])
            cP, cQ = cofactor * P, cofactor * Q
            if cP.weil_pairing(cQ, factors[i][0]) == 1:
                check = False
                break
        if check : break
    
    pairing_value = P.weil_pairing(Q, N)
    for i in range(len(factors)):
        cofactor = N // factors[i][0]
        assert pairing_value^cofactor != 1


    assert (N*P).is_zero() and (N*Q).is_zero()
    assert pairing_value^N == 1

    return P, Q

# find a, b such that aP + bQ = R
# P, Q are the basis of the curve E
def xyBIDIM(P, Q, R, order: Integer):
    x = P.weil_pairing(R, order)
    y = Q.weil_pairing(R, order)

    if x == 1:
        return P.discrete_log(R), 0

    if y == 1:
        return 0, Q.discrete_log(R)

    R_order = R.order()
    R_order_factor = R_order.factor()
    x_order_factor, y_order_factor = [], []

    for fact in R_order_factor:
        cofactor_exp = 0
        cand_order = R_order
        while True:
            if x ^ cand_order != 1:
                break
            cofactor_exp += 1
            cand_order /= fact[0]
        x_order_factor.append(fact[1] - cofactor_exp + 1)

        cofactor_exp = 0
        cand_order = R_order
        while True:
            if y ^ cand_order != 1:
                break
            cofactor_exp += 1
            cand_order /= fact[0]
        y_order_factor.append(fact[1] - cofactor_exp + 1)

    a, b = 1, 1
    discrete_order = 1
    for i in range(len(y_order_factor)):
        if x_order_factor[i] > y_order_factor[i]:
            a *= R_order_factor[i][0] ^ (x_order_factor[i] - y_order_factor[i])
        elif y_order_factor[i] > x_order_factor[i]:
            b *= R_order_factor[i][0] ^ (y_order_factor[i] - x_order_factor[i])
        discrete_order *= R_order_factor[i][0] ^ (
            min(y_order_factor[i], x_order_factor[i]))

    ax, by = x ^ a, y ^ b
    r = discrete_log(ax, by, discrete_order)
    S = a*P - r*b*Q
    k = S.discrete_log(R)
    assert R == k*a*P - k*r*b*Q
    return k*a, -k*r*b


# Cylic isogeny
@dataclass
class Isogeny:
    domain_coeff: FiniteFieldElement
    codomain_coeff: FiniteFieldElement
    domain_curve: EllipticCurve
    codomain_curve: EllipticCurve
    kernel: EllipticCurvePoint
    domain_P: EllipticCurvePoint
    codomain_P: EllipticCurvePoint
    domain_Q: EllipticCurvePoint
    codomain_Q: EllipticCurvePoint
    basis_order: Integer
    degree: Integer

    def __initial_computation(self):
        self.degree = ell
        self.domain_P, self.domain_Q = get_basis(self.domain_curve, self.basis_order)
        eval_point = self.domain_P[0], self.domain_Q[0]

        hs_1, hs_2 = Fp(1), Fp(1)
        hs_P1, hs_P2 = Fp(1), Fp(1)
        hs_Q1, hs_Q2 = Fp(1), Fp(1)
        T = self.kernel
        for _ in range((self.degree - 1)//2):
            hs_1 *= (1-T[0])
            hs_2 *= (-1-T[0])
            hs_P1 *= (eval_point[0] - T[0])
            hs_P2 *= (eval_point[0] ^ (-1) - T[0])
            hs_Q1 *= (eval_point[1] - T[0])
            hs_Q2 *= (eval_point[1] ^ (-1) - T[0])

            T += 2 * self.kernel
        d = (((self.domain_coeff - 2) / (self.domain_coeff + 2))
             ^ self.degree) * (hs_1 / hs_2) ^ 8

        self.codomain_coeff = 2*((1+d)/(1-d))

        self.codomain_curve = EllipticCurve(
            Fp, [0, self.codomain_coeff, 0, 1, 0])

        self.codomain_P = self.codomain_curve.lift_x(
            eval_point[0] ^ self.degree * (hs_P2 / hs_P1) ^ 2)
        self.codomain_Q = self.codomain_curve.lift_x(
            eval_point[1] ^ self.degree * (hs_Q2 / hs_Q1) ^ 2)

        domain_pairing = self.domain_P.weil_pairing(self.domain_Q, self.basis_order)
        codomain_pairing = self.codomain_P.weil_pairing(self.codomain_Q, self.basis_order)
        if domain_pairing ^ self.degree != codomain_pairing:
            self.codomain_P = -self.codomain_P
            assert domain_pairing ^ self.degree * codomain_pairing == 1
        else:
            assert domain_pairing ^ self.degree == codomain_pairing

    def __init__(self, coeff: FiniteFieldElement, kernel: EllipticCurvePoint, basis_order: Integer):
        self.domain_curve = EllipticCurve(Fp, [0, coeff, 0, 1, 0])
        assert self.domain_curve.is_on_curve(kernel[0], kernel[1]) or kernel.is_zero(
        ), "The kernel point must be on the curve"
        self.domain_coeff, self.kernel, self.basis_order = coeff, kernel, basis_order
        assert (ell * kernel).is_zero(), "The degree of isogeny can be ell only"
        self.__initial_computation()

    def velu_eval(self, point: EllipticCurvePoint) -> EllipticCurvePoint:
        hs_P1, hs_P2 = Fp(1), Fp(1)
        point_x = point[0]

        T = self.kernel
        for _ in range((self.degree - 1)//2):
            hs_P1 *= (point_x - T[0])
            hs_P2 *= (point_x ^ (-1) - T[0])
            T += 2 * self.kernel
        
        if hs_P1 == 0: return self.codomain_curve(0)

        return self.codomain_curve.lift_x(
            point_x ^ self.degree * (hs_P2 / hs_P1) ^ 2)

    def eval(self, point: EllipticCurvePoint) -> EllipticCurvePoint:
        if point.is_zero():
            return self.codomain_curve(0)
        try:
            point = self.domain_curve((point[0], point[1]))
        except:
            raise "The point must be on the domain curve"

        assert (point * self.basis_order).is_zero()
        # a, b = xyBIDIM(self.domain_P, self.domain_Q, point)
        # assert point == a * self.domain_P + b * self.domain_Q
        # R = a * self.codomain_P + b * self.codomain_Q
        R = self.velu_eval(point)
        P, Q = self.domain_P, self.domain_Q
        cP, cQ = self.codomain_P, self.codomain_Q
        domain_pairing_1 = P.weil_pairing(point, self.basis_order)
        domain_pairing_2 = Q.weil_pairing(point, self.basis_order)
        codomain_pairing_1 = cP.weil_pairing(R, self.basis_order)
        codomain_pairing_2 = cQ.weil_pairing(R, self.basis_order)

        if not (domain_pairing_1^self.degree == codomain_pairing_1 and domain_pairing_2^self.degree == codomain_pairing_2):
            R = -R
            assert domain_pairing_1^self.degree * codomain_pairing_1 == 1 and domain_pairing_2^self.degree * codomain_pairing_2 == 1
        else:
            assert domain_pairing_1^self.degree == codomain_pairing_1 and domain_pairing_2^self.degree == codomain_pairing_2
        return R

    def dual_isogeny(self):
        cofactor = self.basis_order // self.degree
        codomain_P = cofactor * self.codomain_P
        codomain_Q = cofactor * self.codomain_Q
        assert (not codomain_P.is_zero()) or (not codomain_Q.is_zero())
        if codomain_P.is_zero():
            return Isogeny(self.codomain_coeff, codomain_Q, self.basis_order)
        else:
            return Isogeny(self.codomain_coeff, codomain_P, self.basis_order)


class IsogenyChain:
    chain: list = []
    domain_curve: EllipticCurve
    codomain_curve: EllipticCurve
    degree: Integer

    def __init__(self, _chain: list):
        self.chain = _chain
        self.codomain_curve = _chain[-1].codomain_curve
        self.domain_curve = _chain[0].domain_curve
        self.degree = 1
        for deg in [c.degree for c in self.chain]:
            self.degree *= deg

    def append_forward(self, forward):
        assert forward.domain_curve.defining_polynomial() == self.codomain_curve.defining_polynomial(), "The codomain and domain curve don't match"
        self.chain.append(forward)
        self.codomain_curve = forward.codomain_curve
        self.degree *= forward.degree

    def append_backward(self, backward):
        assert backward.codomain_curve.defining_polynomial() == self.domain_curve.defining_polynomial(), "The codomain and domain curve don't match"
        self.chain.insert(0, backward)
        self.domain_curve = backward.domain_curve
        self.degree *= backward.degree


    def eval(self, point: EllipticCurvePoint) -> EllipticCurvePoint:
        for isog in self.chain:
            point = isog.eval(point)
        return point

# Evaluate a point of E0 through a O0 endomorphism
# only 2 is available as denominator


def O0_eval_endomorphism(O0_element: QuaternionAlgebraElement, point: EllipticCurvePoint, order: Integer) -> EllipticCurvePoint:
    try:
        point = E0((point[0], point[1]))
    except:
        raise "point is not on the curve E0"
    assert (point * order).is_zero()

    baseP, baseQ = get_basis(E0, order * 2)
    a, b = xyBIDIM(baseP, baseQ, point, order*2)

    assert a%2 == 0 and b%2 == 0
    sqrt_point = Integer(a/2)*baseP + Integer(b/2)*baseQ
    assert point == 2*sqrt_point

    point = sqrt_point
    # assert order % 2 == 1, "The order of the point must be odd"
    assert (point * order * 2).is_zero()

    # O0_element = a + b*i + c*j + d*k
    coeff = [(x*2) % (2*order) for x in O0_element.coefficient_tuple()]
    R = E0(0)
    for j in range(4):
        if j == 0: Q = point
        elif j == 1:
            Q = E0(-point[0], point[1]*Fp_i)
        elif j == 2:
            Q = E0(point[0] ^ prime, point[1] ^ prime)
        elif j == 3:
            Q = E0((-point[0]) ^ prime, -(point[1]*Fp_i) ^ prime)
        R = R + Integer(coeff[j]) * Q

    assert (R * order).is_zero()

    return R

#
# Take as input an ideal I and output the generator R of the corresponding isogeny kernel
#
def left_O0_ideal_to_isogeny_kernel(ideal: QuaternionAlgebraIdeal) -> EllipticCurvePoint:
    norm = Integer(ideal.norm())
    P, Q = get_basis(E0, norm)
    assert (P*norm).is_zero() and (Q*norm).is_zero(), '1'
    assert P.weil_pairing(Q, norm) != 1, '2'

    generator = ideal_generator(ideal)

    P_eval, Q_eval = O0_eval_endomorphism(
        generator, P, norm), O0_eval_endomorphism(generator, Q, norm)
    assert (P_eval * norm).is_zero() and (Q_eval * norm).is_zero(), '3'
    assert (P_eval == E0(0) or Q_eval == E0(0)
            or P_eval.weil_pairing(Q_eval, norm) == 1), '4'

    if P_eval.is_zero():
        return P
    elif Q_eval.is_zero():
        return Q

    x = P_eval.discrete_log(Q_eval)
    assert (Q_eval - P_eval * x).is_zero()
    return Q - Integer(x) * P

#
# Push Endomorphism through an isogeny from E0
#
def eval_endomorphism(O1_element, point: EllipticCurvePoint, order: Integer, E0_isogeny: IsogenyChain, E0_dual_isogeny: IsogenyChain) -> EllipticCurvePoint:
    E1 = E0_isogeny.codomain_curve
    assert E1.is_on_curve(point[0], point[1]) or point.is_zero(
    ), "point is not on the curve E1"
    if point.is_zero():
        return E1(0)
    
    assert (order * point).is_zero(), "The order is wrong"
    assert E0_isogeny.chain[0].basis_order % order == 0, "The point can't be evaluated using given isogeny"
    assert E0_dual_isogeny.chain[0].basis_order % order == 0, "The point can't be evaluated using given isogeny"

    isogeny_degree = E0_isogeny.degree
    assert gcd(order, isogeny_degree) == 1, "The point cannot be evaluated"

    N_O1_element = isogeny_degree * O1_element
    coordinate = O0_coordinate(N_O1_element)
    O0_basis = O0.basis()

    assert N_O1_element == coordinate[0]*O0_basis[0] + coordinate[1]*O0_basis[1] + coordinate[2]*O0_basis[2] + coordinate[3]*O0_basis[3], "The coordinate is wrong"

    result_point = E1(0)

    for i in range(4):
        if coordinate[i] == 0:
            continue
        eval_point = point
        eval_point = E0_dual_isogeny.eval(eval_point)
        assert E0_dual_isogeny.codomain_curve.is_on_curve(
            eval_point[0], eval_point[1]), "Unreachable : point is not on E0"
        eval_point = O0_eval_endomorphism(O0_basis[i], eval_point, order)
        eval_point = E0_isogeny.eval(eval_point)
        r = (mod(isogeny_degree, order) ^ (-2))
        result_point = result_point + \
            Integer(coordinate[i]) * Integer(r) * eval_point

    return result_point
