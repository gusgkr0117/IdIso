import random
load('quaternion_tools.sage')
load('isogeny.sage')
load('richelot.sage')
load('const.sage')
load('../01. jacobian_isogeny/22_isogeny.sage')
load('../01. jacobian_isogeny/33_isogeny.sage')

def cornacchia(d, m):
    try: 
        (x,y) = DiagonalQuadraticForm(QQ, [1,d]).solve(m)
        if not x.is_integer() or not y.is_integer() : raise Exception("No solution")
        return x, y
    except: raise Exception("No solution")

# 1. Get Random Ideal of norm ell^e
I = GetRandomIdealElle()
assert(I.norm() == ell^6)


# 2. Extract the first ideal factor I_1
ellO0 = QA.ideal(O0.basis()).scale(ell)
I1 = AddIdeal(I, ellO0)

# 3. Compute corresponding isogeny
phi1_kernel_generator = left_O0_ideal_to_isogeny_kernel(I1)
phi1 = Isogeny(Fp(0), phi1_kernel_generator, 2^e1*3^e2*ell)
assert(I1.norm() == ell)

# 4. Get the codomain curve E1 and dual isogeny phi1_dual
E1 = phi1.codomain_curve
phi1_dual = phi1.dual_isogeny()

# 4-1. Adjust the error [-1]
cofactor = phi1_dual.domain_P.order() // 3^16
T = cofactor * phi1_dual.codomain_P
ellT = phi1.eval(T)
if ellT != phi1.degree * cofactor * phi1_dual.domain_P:
    phi1_dual.codomain_P *= -1
    phi1_dual.codomain_Q *= -1
    assert -ellT == phi1.degree * cofactor * phi1_dual.domain_P
else: assert ellT == phi1.degree * cofactor * phi1_dual.domain_P

T = cofactor * phi1.codomain_P
ellT = phi1_dual.eval(T)
assert ellT == phi1_dual.degree * cofactor * phi1.domain_P

def GetAlphaBeta(I, N, O_basis):
    I_basis = GetReducedBasis(I.basis())
    I_generator = I_basis[2]
    e1 = 148
    e2 = 16
    gram = matrix([[1,0,0,0],[0,1,0,0],[0,0,prime,0],[0,0,0,prime]])
    M_O = matrix([vector(v.coefficient_tuple()) for v in O_basis])
    G = M_O * gram * M_O.transpose()

    x,y = 0, 0
    k = 100
    for i in range(k^2):
        alpha = I_generator + random.randint(-k, k) * I_basis[1] + random.randint(-k, k) * I_basis[0]
        if gcd(alpha.reduced_norm(), N) != 1: continue
        target = N - alpha.reduced_norm()
        assert target > 0
        if kronecker(-G[1][1], target) != 1: continue
        try:
            x,y = cornacchia(G[1][1], target)
            break
        except:
            continue
    beta = O_basis[0]*x + O_basis[1]*y
    assert (beta.reduced_norm() + alpha.reduced_norm()) == N
    assert gcd(beta.reduced_norm(), alpha.reduced_norm()) == 1
    return alpha, beta

def IdealToIsogenySmall(I, ell, isoChain, isoChainDual, e1, e2):
    assert I.norm() == ell
    I_gen = ideal_generator(I)
    O_right = I.right_order()
    O_left = I.left_order()
    E_domain = isoChain.codomain_curve
    O_left_basis = GetReducedBasis(O_left.basis())

    N = 2^e1*3^e2

    # Computing alpha and beta
    alpha, beta = GetAlphaBeta(I, N, O_left_basis)

    # Computing x = n(beta)^-1 mod N
    N_alpha = alpha.reduced_norm()
    N_beta = beta.reduced_norm()
    x_value = Integer(mod(N_beta, N)^-1)

    # Get basis
    P, Q = get_basis(E_domain, N)

    # Evaluate the endomorphism
    psi_P = eval_endomorphism(x_value * alpha * beta, P, N, isoChain, isoChainDual)
    psi_Q = eval_endomorphism(x_value * alpha * beta, Q, N, isoChain, isoChainDual)

    # Check if the kernel is maximally isotropic
    points = [P, Q, psi_P, psi_Q]
    points = [E_domain((e[0], e[1])) for e in points]
    assert points[0].weil_pairing(points[1], N)*points[2].weil_pairing(points[3], N) == 1
    [ell_P, ell_Q] = get_basis(E_domain, ell)
    points = points + [ell_P, ell_Q]

    # Computing the (2,2) and (3,3) - isogenies between hyperelliptic curves
    ## 1. (2,2)-Gluing
    points = [(points[0], points[2]), (points[1], points[3]), (points[4], E_domain(0)), (points[5], E_domain(0))]
    kernel2 = [(3^e2*2^(e1-1)*D[0], 3^e2*2^(e1-1)*D[1]) for D in [points[0], points[1]]]
    h, points, isog = Gluing22(E_domain, E_domain, kernel2, eval_points = points)
    
    ## 2. Richelot (2,2)-isogenies
    kernel22 = [3^e2 * 2 * D for D in points[:2]]
    j, points = isogeny_22(kernel22, points, e1-2)
    
    ## 3. BFT (3,3)-isogenies
    kernel33 = [2 * D for D in points[:2]]
    j, points = isogeny_33(kernel33, points, e2)
    
    ## 4. Check if the curve is splitting
    G1 = points[0][0]
    G2 = points[1][0]
    h = j.curve().hyperelliptic_polynomials()[0]
    G3, r3 = h.quo_rem(G1*G2)
    assert r3 == 0
    delta = Matrix(G.padded_list(3) for G in (G1, G2, G3))
    assert delta.determinant() == 0, "The curve is not splitted"

    ## 5. Splitting the curve
    kernel22 = [D for D in points[:2]]
    prodE, eval_points = Splitting22(kernel22, [points[2], points[3]])
    assert E_domain.j_invariant() in [T.j_invariant() for T in prodE]

    ## 6. Compute the corresponding kernel
    P, Q = E_domain(0), E_domain(0)
    if prodE[0].j_invariant() == E_domain.j_invariant():
        P, Q = eval_points[0][0], eval_points[1][0]
    else:
        P, Q = eval_points[0][1], eval_points[1][1]

    kernel = E_domain(0)
    if P.is_zero(): kernel = ell_Q
    elif Q.is_zero(): kernel = ell_P
    else:
        assert P.weil_pairing(Q, P.order()) == 1

        r = P.discrete_log(Q)
        kernel = ell_P * r - ell_Q
    
    return kernel

# 1. Compute the right order O1
O1 = I1.right_order()

# 2. Extract the next ideal factor
I2 = I1.conjugate() * I
I2 = I2.scale(1/ell)
ellO1 = QA.ideal(O1.basis()).scale(ell)
I2 = AddIdeal(I2, ellO1)

assert(I2.norm() == ell and I2.left_order() == O1)

isog1 = IsogenyChain([phi1])
isog1_dual = IsogenyChain([phi1_dual])
next_kernel = IdealToIsogenySmall(I2, ell, isog1, isog1_dual, 148, 16)