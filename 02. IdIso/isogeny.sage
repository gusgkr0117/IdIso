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

# Cylic isogeny
@dataclass
class Isogeny : 
    domain_coeff : FiniteFieldElement
    codomain_coeff : FiniteFieldElement
    domain_curve : EllipticCurve
    codomain_curve : EllipticCurve
    kernel : EllipticCurvePoint
    domain_P : EllipticCurvePoint
    codomain_P : EllipticCurvePoint
    domain_Q : EllipticCurvePoint
    codomain_Q : EllipticCurvePoint
    degree : Integer

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
            hs_P2 *= (eval_point[0]^(-1) - T[0])
            hs_Q1 *= (eval_point[1] - T[0])
            hs_Q2 *= (eval_point[1]^(-1) - T[0])

            T += 2 * self.kernel
        d = (((self.domain_coeff - 2) / (self.domain_coeff + 2))^self.degree) * (hs_1 / hs_2)^8
    
        self.codomain_coeff = 2*((1+d)/(1-d))

        self.codomain_curve = EllipticCurve(Fp, [0, self.codomain_coeff, 0, 1, 0])

        self.codomain_P = self.codomain_curve.lift_x(eval_point[0]^self.degree * (hs_P2 / hs_P1)^2)
        self.codomain_Q = self.codomain_curve.lift_x(eval_point[1]^self.degree * (hs_Q2 / hs_Q1)^2)

    def __init__(self, coeff : FiniteFieldElement, kernel : EllipticCurvePoint):
        self.domain_curve = EllipticCurve(Fp, [0, coeff, 0, 1, 0]) 
        assert self.domain_curve.is_on_curve(kernel[0], kernel[1]) or kernel.is_zero(), "The kernel point must be on the curve"
        self.domain_coeff, self.kernel = coeff, kernel
        self.__initial_computation()

    def eval(self, point : EllipticCurvePoint) -> EllipticCurvePoint:
        assert self.domain_curve.is_on_curve(point[0], point[1]) or point.is_zero(), "The point must be on the domain curve"
        if point.is_zero() : return self.codomain_curve(0)
        
        x = self.domain_P.weil_pairing(point, E0_order)
        y = self.domain_Q.weil_pairing(point, E0_order)

        order_x = x.multiplicative_order()
        order_y = y.multiplicative_order()

        assert order_x % order_y == 0 or order_y % order_x == 0, "Unreachable"

        if order_x % order_y == 0 :
            m = y.log(x)
            R = m * self.domain_P - self.domain_Q
            assert R.weil_pairing(point, E0_order) == 1, "Unreachable : The input point must be linear to R"
            r = R.discrete_log(point)
            return r * m * self.codomain_P - r * self.codomain_Q
        else :
            m = x.log(y)
            R = m * self.domain_Q - self.domain_P
            assert R.weil_pairing(point, E0_order) == 1, "Unreachable : The input point must be linear to R"
            r = R.discrete_log(point)
            return r * m * self.codomain_Q - r * self.codomain_P

    def dual_isogeny(self):
        cofactor_P = self.codomain_P.order() // self.degree
        cofactor_Q = self.codomain_Q.order() // self.degree
        R = cofactor_P * self.codomain_P + cofactor_Q * self.codomain_Q
        if R.is_zero() :
            if not self.codomain_P.is_zero(): R = cofactor_P * self.codomain_P
            else : R = cofactor_Q * self.codomain_Q

        order = R.order()
        assert order % self.degree == 0, "Unreachable : order is wrong"
        cofactor = order // self.degree

        return Isogeny(self.codomain_coeff, cofactor * R)


## Evaluate a point of E0 through a O0 endomorphism
def O0_eval_endomorphism(O0_element : QuaternionAlgebraElement, point : EllipticCurvePoint) -> EllipticCurvePoint:
    assert E0.is_on_curve(point[0], point[1]), "point is not on the curve E0"
    order = point.order()
    # assert order % 2 == 1, "The order of the point must be odd"

    # O0_element = a + b*i + c*j + d*k
    coeff = [x % order for x in O0_element.coefficient_tuple()]
    R = E0(0)
    for j in range(4):
        Q = point
        if j == 1: Q = E0(-point[0], point[1]*Fp_i)
        elif j == 2: Q = E0(point[0]^prime, point[1]^prime)
        elif j == 3: Q = E0((-point[0])^prime, (point[1]*Fp_i)^prime)
        R = R + Integer(coeff[j]) * Q

    return R

#
# Take as input an ideal I and output the generator R of the corresponding isogeny kernel
#
def left_O0_ideal_to_isogeny_kernel(ideal : QuaternionAlgebraIdeal) -> EllipticCurvePoint:
    norm = Integer(ideal.norm())
    P, Q = E0.gens()
    cardinality = P.order()
    assert(cardinality % norm == 0)

    cofactor = Integer(cardinality // norm)
    
    P, Q = cofactor * P, cofactor * Q
    assert(P.order() == norm and Q.order() == norm)

    generator = ideal_generator(ideal)

    P_eval, Q_eval = O0_eval_endomorphism(generator, P), O0_eval_endomorphism(generator, Q)
    assert(P_eval == E0(0) or Q_eval == E0(0) or P_eval.weil_pairing(Q_eval, norm) == 1)

    if P_eval.is_zero() : return P
    elif Q_eval.is_zero() : return Q
    
    x = P_eval.discrete_log(Q_eval)
    return Q - Integer(x) * P

# 
# Push Endomorphism through an isogeny from E0
#
def eval_endomorphism(O1_element, point : EllipticCurvePoint, E0_isogeny : Isogeny) -> EllipticCurvePoint:
    E1 = E0_isogeny.codomain_curve
    assert E1.is_on_curve(point[0], point[1]) or point.is_zero(), "point is not on the curve E1"
    if point.is_zero() : return E1(0)

    N = E0_isogeny.degree
    order = point.order()
    assert gcd(order, N) == 1, "The point cannot be evaluated"

    N_O1_element = N * O1_element
    coordinate = O0_coordinate(N_O1_element)
    O0_basis = O0.basis()

    print("coordinate :", coordinate)

    result_point = E1(0)
    for i in range(4):
        if coordinate[i] == 0: continue
        
        dual_isogeny = E0_isogeny.dual_isogeny()
        point = dual_isogeny.eval(point)
        assert E0.is_on_curve(point[0], point[1]), "Unreachable : point is not on E0"
        point = O0_eval_endomorphism(O0_basis[i], point)
        point = E0_isogeny.eval(point)
        r = mod(N, order)^(-2) * mod(coordinate[i], order)
        result_point = result_point + Integer(r) * point

    return result_point