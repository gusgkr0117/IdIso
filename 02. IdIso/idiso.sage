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
        (x,y) = DiagonalQuadraticForm(QQ, [1,d]).solve(m)
        if not x.is_integer() or not y.is_integer() : raise Exception("No solution")
        return x, y
    except: raise Exception("No solution")

# Get Random Ideal of norm ell^e
I = GetRandomIdealElle()
assert(I.norm() == ell^6)

# Extract the first ideal factor I_1
ellO0 = QA.ideal(O0.basis()).scale(ell)
I1 = AddIdeal(I, ellO0)

phi1_kernel_generator = left_O0_ideal_to_isogeny_kernel(I1)
phi1 = Isogeny(Fp(0), phi1_kernel_generator)

E1 = phi1.codomain_curve
phi1_dual = phi1.dual_isogeny()

assert(I1.norm() == ell)

O1 = I1.right_order()

I2 = I1.conjugate() * I
I2 = I2.scale(1/ell)
ellO1 = QA.ideal(O1.basis()).scale(ell)
I2 = AddIdeal(I2, ellO1)

assert(I2.norm() == ell and I2.left_order() == O1)

I2_generator = ideal_generator(I2)

O1_basis = GetReducedBasis(O1.basis())

endomorphism_1 = 0
for v in O1_basis:
    if v.reduced_norm() != 1: endomorphism_1 = O1_basis[1]

x,y = 0,0
while True:
    endomorphism_1 = [random.randint(-5,5) * v for v in O1_basis]
    endomorphism_1 = endomorphism_1[0] + endomorphism_1[1] + endomorphism_1[2] + endomorphism_1[3]
    
    if endomorphism_1.reduced_norm() == 1 or endomorphism_1.reduced_norm() % 2 == 0 : continue
    print("endomorphism_1 :", endomorphism_1, endomorphism_1.reduced_norm())
    x,y = 0,0
    e = floor(log(endomorphism_1.reduced_norm(),2)) + 1
    while ((prime + 1)^2) % (2^e) == 0:    
        # while True:
        #     random_v = vector([random.randint(-5,5) for _ in range(4)])
        #     alpha2 = random_v * vector(I2_basis)
        #     if alpha2.reduced_norm() % ell^2 != 0 : break

        M1 = GetCoeff(O1)

        gram = matrix([[1,0,0,0],[0,1,0,0],[0,0,prime,0],[0,0,0,prime]])
        O1_basis = GetReducedBasis(O1.basis())
        M_O1 = matrix([vector(v.coefficient_tuple()) for v in O1_basis])
        G = M_O1 * gram * M_O1.transpose()
        print(G)
        print(endomorphism_1, endomorphism_1.reduced_norm().factor())
        
        target = 2^e - endomorphism_1.reduced_norm()
        print(target.factor())
        if kronecker(-G[1][1], target) != 1:
            print("There is no solution.")
            e+=1
            continue

        try : 
            x,y = cornacchia(G[1][1], 2^e - endomorphism_1.reduced_norm())
            break
        except :
            print(2^e - endomorphism_1.reduced_norm())
            e+=1
    if x !=0 or y!=0 : break
    
beta = O1_basis[0] * x + O1_basis[1] * y

print("beta :", beta)
P_2e, Q_2e = E1.gens()
assert (prime + 1) % (2^e) == 0, "2^e is not accessible"
cofactor = (prime + 1) // (2^e)
P_2e, Q_2e = cofactor * P_2e, cofactor * Q_2e

beta_P = eval_endomorphism(beta, P_2e, phi1)