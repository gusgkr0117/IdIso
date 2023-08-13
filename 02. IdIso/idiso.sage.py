

# This file was *autogenerated* from the file idiso.sage
from sage.all_cmdline import *   # import sage library

_sage_const_1 = Integer(1); _sage_const_6 = Integer(6); _sage_const_0 = Integer(0); _sage_const_4 = Integer(4); _sage_const_2 = Integer(2)
import random
from sage.algebras.quatalg.quaternion_algebra import basis_for_quaternion_lattice
from sage.algebras.quatalg.quaternion_algebra_element import QuaternionAlgebraElement_rational_field as QuaternionAlgebraElement
from sage.algebras.quatalg.quaternion_algebra import QuaternionFractionalIdeal_rational as QuaternionAlgebraIdeal
from sage.schemes.elliptic_curves.ell_point import EllipticCurvePoint_finite_field as EllipticCurvePoint

load('quaternion_tools.sage')
load('isogeny.sage')
load('richelot.sage')
load('const.sage')

def cornacchia(d, m):
    try: 
        (x,y) = DiagonalQuadraticForm(QQ, [_sage_const_1 ,d]).solve(m)
        if not x.is_integer() or not y.is_integer() : raise Exception("No solution")
        return x, y
    except: raise Exception("No solution")

I = GetRandomIdealElle()

assert(I.norm() == ell**_sage_const_6 )

ellO0 = QA.ideal(O0.basis()).scale(ell)
I1 = AddIdeal(I, ellO0)

phi1_kernel_generator = left_O0_ideal_to_isogeny_kernel(I1)
phi1 = Isogeny(Fp(_sage_const_0 ), phi1_kernel_generator)

E1 = phi1.codomain_curve
phi1_dual = phi1.dual_isogeny()

assert(I1.norm() == ell)

O1 = I1.right_order()

I2 = I1.conjugate() * I
I2 = I2.scale(_sage_const_1 /ell)
ellO1 = QA.ideal(O1.basis()).scale(ell)
I2 = AddIdeal(I2, ellO1)

assert(I2.norm() == ell and I2.left_order() == O1)

I2_basis = GetReducedBasis(I2.basis())
O1_ell = QA.ideal(O1.basis()).scale(ell)
alpha2 = _sage_const_0 
for i in range(_sage_const_4 ):
    if not IdealContains(O1_ell, I2_basis[i]):
        alpha2 = I2_basis[i]

O1_basis = GetReducedBasis(O1.basis())

endomorphism_1 = _sage_const_0 
for v in O1_basis:
    if v.reduced_norm() != _sage_const_1 : endomorphism_1 = O1_basis[_sage_const_1 ]

e = floor(log(endomorphism_1.reduced_norm(),_sage_const_2 )) + _sage_const_1 
while True:    
    # while True:
    #     random_v = vector([random.randint(-5,5) for _ in range(4)])
    #     alpha2 = random_v * vector(I2_basis)
    #     if alpha2.reduced_norm() % ell^2 != 0 : break

    M1 = GetCoeff(O1)

    gram = matrix([[_sage_const_1 ,_sage_const_0 ,_sage_const_0 ,_sage_const_0 ],[_sage_const_0 ,_sage_const_1 ,_sage_const_0 ,_sage_const_0 ],[_sage_const_0 ,_sage_const_0 ,prime,_sage_const_0 ],[_sage_const_0 ,_sage_const_0 ,_sage_const_0 ,prime]])
    O1_basis = GetReducedBasis(O1.basis())
    M_O1 = matrix([vector(v.coefficient_tuple()) for v in O1_basis])
    G = M_O1 * gram * M_O1.transpose()
    print(G)
    print(endomorphism_1, endomorphism_1.reduced_norm().factor())
    
    target = _sage_const_2 **e - endomorphism_1.reduced_norm()
    if kronecker(-_sage_const_1 , target) != _sage_const_1 :
        print("There is no solution.")
        e+=_sage_const_1 
        continue

    try : 
        x,y = cornacchia(G[_sage_const_1 ][_sage_const_1 ], _sage_const_2 **e - endomorphism_1.reduced_norm())
        break
    except :
        print(_sage_const_2 **e - endomorphism_1.reduced_norm())
        e+=_sage_const_1 

beta = O1_basis[_sage_const_0 ] * x + O1_basis[_sage_const_1 ] * y

P_2e, Q_2e = E1.gens()
assert (prime + _sage_const_1 ) % (_sage_const_2 **e) == _sage_const_0 , "2^e is not accessible"
cofactor = (prime + _sage_const_1 ) // (_sage_const_2 **e)
P_2e, Q_2e = cofactor * P_2e, cofactor * Q_2e

beta_P = eval_endomorphism(beta, P_2e, phi1)

