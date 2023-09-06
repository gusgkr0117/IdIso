from dataclasses import dataclass

from sage.algebras.quatalg.quaternion_algebra import basis_for_quaternion_lattice
from sage.algebras.quatalg.quaternion_algebra_element import QuaternionAlgebraElement_rational_field as QuaternionAlgebraElement
from sage.algebras.quatalg.quaternion_algebra import QuaternionFractionalIdeal_rational as QuaternionAlgebraIdeal
from sage.schemes.elliptic_curves.ell_point import EllipticCurvePoint_finite_field as EllipticCurvePoint
from sage.schemes.elliptic_curves.ell_finite_field import EllipticCurve_finite_field as EllipticCurve

from sage.rings.finite_rings.element_pari_ffelt import FiniteFieldElement_pari_ffelt as FiniteFieldElement
from sage.rings.integer import Integer

load('const.sage')
load('quaternion_tools.sage')

# find a, b such that aP + bQ = R
# P, Q are the basis of the curve E


def xyBIDIM(P, Q, R):
    x = P.weil_pairing(R, E0_order)
    y = Q.weil_pairing(R, E0_order)

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
    degree: Integer

    def __initial_computation(self):
        self.degree = self.kernel.order()
        self.domain_P, self.domain_Q = self.domain_curve.gens()

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

    def __init__(self, coeff: FiniteFieldElement, kernel: EllipticCurvePoint):
        self.domain_curve = EllipticCurve(Fp, [0, coeff, 0, 1, 0])
        assert self.domain_curve.is_on_curve(kernel[0], kernel[1]) or kernel.is_zero(
        ), "The kernel point must be on the curve"
        self.domain_coeff, self.kernel = coeff, kernel
        self.__initial_computation()

    def eval(self, point: EllipticCurvePoint) -> EllipticCurvePoint:
        if point.is_zero():
            return self.codomain_curve(0)
        try:
            point = self.domain_curve((point[0], point[1]))
        except:
            raise "The point must be on the domain curve"
        a, b = xyBIDIM(self.domain_P, self.domain_Q, point)
        assert point == a * self.domain_P + b * self.domain_Q
        R = a * self.codomain_P + b * self.codomain_Q
        return R

    def dual_isogeny(self):
        cofactor = self.domain_P.order() // self.degree
        R = cofactor * self.codomain_P + cofactor * self.codomain_Q
        print("kernel of dual :", R.order())
        order = R.order()
        assert order == self.degree, "Unreachable : order is wrong"
        return Isogeny(self.codomain_coeff, R)


# Evaluate a point of E0 through a O0 endomorphism
# only 2 is available as denominator
def O0_eval_endomorphism(O0_element: QuaternionAlgebraElement, point: EllipticCurvePoint) -> EllipticCurvePoint:
    try:
        point = E0((point[0], point[1]))
    except:
        raise "point is not on the curve E0"
    baseP, baseQ = E0.gens()
    a, b = xyBIDIM(baseP, baseQ, point)

    sqrt_point = Integer(a/2)*baseP + Integer(b/2)*baseQ
    assert point == 2*sqrt_point

    point = sqrt_point

    order = point.order()
    # assert order % 2 == 1, "The order of the point must be odd"

    # O0_element = a + b*i + c*j + d*k
    coeff = [(x*2) % order for x in O0_element.coefficient_tuple()]
    R = E0(0)
    for j in range(4):
        Q = point
        if j == 1:
            Q = E0(-point[0], point[1]*Fp_i)
        elif j == 2:
            Q = E0(point[0] ^ prime, point[1] ^ prime)
        elif j == 3:
            Q = E0((-point[0]) ^ prime, (point[1]*Fp_i) ^ prime)
        R = R + Integer(coeff[j]) * Q

    return R

#
# Take as input an ideal I and output the generator R of the corresponding isogeny kernel
#


def left_O0_ideal_to_isogeny_kernel(ideal: QuaternionAlgebraIdeal) -> EllipticCurvePoint:
    norm = Integer(ideal.norm())
    P, Q = E0.gens()
    cardinality = P.order()
    assert (cardinality % norm == 0)

    cofactor = Integer(cardinality // norm)

    P, Q = cofactor * P, cofactor * Q
    assert (P.order() == norm and Q.order() == norm)

    generator = ideal_generator(ideal)

    P_eval, Q_eval = O0_eval_endomorphism(
        generator, P), O0_eval_endomorphism(generator, Q)
    assert (P_eval == E0(0) or Q_eval == E0(0)
            or P_eval.weil_pairing(Q_eval, norm) == 1)

    if P_eval.is_zero():
        return P
    elif Q_eval.is_zero():
        return Q

    x = P_eval.discrete_log(Q_eval)
    return Q - Integer(x) * P

#
# Push Endomorphism through an isogeny from E0
#


def eval_endomorphism(O1_element, point: EllipticCurvePoint, E0_isogeny: Isogeny, E0_dual_isogeny: Isogeny) -> EllipticCurvePoint:
    E1 = E0_isogeny.codomain_curve
    assert E1.is_on_curve(point[0], point[1]) or point.is_zero(
    ), "point is not on the curve E1"
    if point.is_zero():
        return E1(0)

    isogeny_degree = E0_isogeny.degree
    order = point.order()
    assert gcd(order, isogeny_degree) == 1, "The point cannot be evaluated"

    N_O1_element = isogeny_degree * O1_element
    coordinate = O0_coordinate(N_O1_element)
    O0_basis = O0.basis()

    print(coordinate)

    result_point = E1(0)

    for i in range(4):
        if coordinate[i] == 0:
            continue
        eval_point = point
        eval_point = E0_dual_isogeny.eval(eval_point)
        assert E0_dual_isogeny.codomain_curve.is_on_curve(
            eval_point[0], eval_point[1]), "Unreachable : point is not on E0"
        eval_point = O0_eval_endomorphism(O0_basis[i], eval_point)
        eval_point = E0_isogeny.eval(eval_point)
        r = (mod(isogeny_degree, order) ^ (-2))
        result_point = result_point + \
            Integer(coordinate[i]) * Integer(r) * eval_point

    return result_point
