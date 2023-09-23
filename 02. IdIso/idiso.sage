import random
load('const.sage')
load('quaternion_tools.sage')
load('isogeny.sage')
load('../01. jacobian_isogeny/22_isogeny.sage')
load('../01. jacobian_isogeny/33_isogeny.sage')

def cornacchia(d, m):
    try: 
        (x,y) = DiagonalQuadraticForm(QQ, [1,d]).solve(m)
        if not x.is_integer() or not y.is_integer() : raise Exception("No solution")
        return x, y
    except: raise Exception("No solution")

def GetAlphaBeta(I, N, O_basis):
    I_basis = GetReducedBasis(I.basis())
    I_generator = I_basis[2]
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
    O_left = I.left_order()
    E_domain = isoChain.codomain_curve
    O_left_basis = GetReducedBasis(O_left.basis())

    N = 2^e1*3^e2

    # Computing alpha and beta
    alpha, beta = GetAlphaBeta(I, N, O_left_basis)
    assert IdealContains(I, alpha), "alpha is not contained in the ideal"
    assert IdealContains(QA.ideal(O_left.basis()), beta), "beta is not contained in the ideal"

    print(alpha)
    print(alpha.reduced_norm().factor())
    print(beta)
    print(beta.reduced_norm().factor())

    # Computing x = n(beta)^-1 mod N
    N_beta = beta.reduced_norm()
    x_value = Integer(mod(N_beta, N)^-1)

    # Get basis
    P, Q = get_basis(E_domain, N)

    # Endomorphism TEST
    # testv1, testv2 = QA(3+2*QA_j+QA_k), QA(7+QA_j+3*QA_k)
    # testv1, testv2 = alpha, beta
    # test1_P = eval_endomorphism(testv1, P, N, isoChain, isoChainDual)
    # test1_P = eval_endomorphism(testv2*x_value, test1_P, N, isoChain, isoChainDual)
    # test2_P = eval_endomorphism(x_value*testv2*testv1, P, N, isoChain, isoChainDual)
    # assert test2_P == test1_P, "eval_endomorphism error!"

    # Evaluate the endomorphism
    psi_P = eval_endomorphism(x_value * beta * alpha, P, N, isoChain, isoChainDual)
    psi_Q = eval_endomorphism(x_value * beta * alpha, Q, N, isoChain, isoChainDual)

    # Check if the kernel is maximally isotropic
    points = [P, Q, psi_P, psi_Q]
    points = [E_domain((e[0], e[1])) for e in points]
    assert points[0].weil_pairing(points[1], N)*points[2].weil_pairing(points[3], N) == 1
    [ell_P, ell_Q] = get_basis(E_domain, ell)
    points = points + [ell_P, ell_Q]

    # load('../01. jacobian_isogeny/22_isogeny.sage')
    # Computing the (2,2) and (3,3) - isogenies between hyperelliptic curves
    ## 1. (2,2)-Gluing
    points = [(points[0], points[2]), (points[1], points[3]), (points[4], E_domain(0)), (points[5], E_domain(0))]
    kernel2 = [(3^e2*2^(e1-1)*D[0], 3^e2*2^(e1-1)*D[1]) for D in [points[0], points[1]]]
    h, points, isog = Gluing22(E_domain, E_domain, kernel2, eval_points = points)
    print("after gluing :", h.absolute_igusa_invariants_kohel())

    ## 2. Richelot (2,2)-isogenies
    kernel22 = [3^e2 * 2 * D for D in points[:2]]
    j, points = isogeny_22(kernel22, points, e1-2)
    print("after 22 :", j.curve().absolute_igusa_invariants_kohel())

    # load('../01. jacobian_isogeny/33_isogeny.sage')
    ## 3. BFT (3,3)-isogenies
    kernel33 = [2 * D for D in points[:2]]
    j, points = isogeny_33(kernel33, points, e2)
    print("after 33 :", j.curve().absolute_igusa_invariants_kohel())

    ## 4. Check if the curve is splitting
    G1 = points[0][0]
    G2 = points[1][0]
    h = j.curve().hyperelliptic_polynomials()[0]
    G3, r3 = h.quo_rem(G1*G2)
    assert r3 == 0, "r3 is not zero"
    delta = Matrix(G.padded_list(3) for G in (G1, G2, G3))
    assert delta.determinant() == 0, "The curve is not splitted"

    ## 5. Splitting the curve
    kernel22 = [D for D in points[:2]]
    prodE, eval_points = Splitting22(kernel22, [points[2], points[3]])
    assert E_domain.j_invariant() in [T.j_invariant() for T in prodE], "no E_domain"

    ## 6. Compute the corresponding kernel
    P, Q = E_domain(0), E_domain(0)
    if prodE[0].j_invariant() == E_domain.j_invariant():
        P, Q = eval_points[0][0], eval_points[1][0]
    else:
        P, Q = eval_points[0][1], eval_points[1][1]

    assert (ell*P).is_zero() and (ell*Q).is_zero()
    assert P.curve().j_invariant() == E_domain.j_invariant()
    assert Q.curve().j_invariant() == E_domain.j_invariant()
    
    kernel = E_domain(0)
    if P.is_zero(): kernel = ell_P
    elif Q.is_zero(): kernel = ell_Q
    else:
        assert P.weil_pairing(Q, ell) == 1, "P, Q are not linear"

        r = P.discrete_log(Q)
        kernel = ell_P * r - ell_Q
    
    return kernel


# 1. Get Random Ideal of norm ell^e
I = GetRandomIdealElle()
assert(I.norm() == ell^6)
print("I:", I.basis())

# 2. Extract the first ideal factor I_1
ellO0 = QA.ideal(O0.basis()).scale(ell)
I1 = AddIdeal(I, ellO0)
print("I1 :", I1)

# 3. Compute corresponding isogeny
phi1_kernel_generator = left_O0_ideal_to_isogeny_kernel(I1)        
phi1 = Isogeny(Fp(0), phi1_kernel_generator, 2^e1*3^e2*ell)
assert(I1.norm() == ell)

# 4. Get the codomain curve E1 and dual isogeny phi1_dual
E1 = phi1.codomain_curve
phi1_dual = phi1.dual_isogeny()
print("E1 :", E1)

# 4-1. Adjust the error [-1]
T = phi1_dual.codomain_P
ellT = phi1.eval(T)
if ellT != phi1.degree * phi1_dual.domain_P:
    phi1_dual.codomain_P *= -1
    phi1_dual.codomain_Q *= -1
    assert -ellT == phi1.degree * phi1_dual.domain_P
else: assert ellT == phi1.degree * phi1_dual.domain_P

T = phi1.codomain_P
ellT = phi1_dual.eval(T)
assert ellT == phi1_dual.degree * phi1.domain_P

compI = I1
contI = I
isog_chain = IsogenyChain([phi1])
isog_dual_chain = IsogenyChain([phi1_dual])
for step in range(2, 7):
    # 1. Compute the right order O1
    prevO = compI.right_order()

    # 2. Extract the next ideal factor
    contI = compI.conjugate() * contI
    contI = contI.scale(1/ell)
    ell_prevO = QA.ideal(prevO.basis()).scale(ell)
    compI = AddIdeal(contI, ell_prevO)

    assert compI.norm() == ell and compI.left_order() == prevO

    # 3. Compute Corresponding isogeny
    kernel_generator = None
    for attempt in range(3):
        try:
            kernel_generator = IdealToIsogenySmall(compI, ell, isog_chain, isog_dual_chain, e1, e2)
            print("[INFO] I%d to phi%d succeed"%(step, step))
            break
        except Exception as e:
            print("[ERROR] I%d to phi%d failed"%(step, step), e)
    if kernel_generator == None : exit()
    phi_compI = Isogeny(isog_chain.chain[-1].codomain_coeff, kernel_generator, 2^e1*3^e2*ell)

    # 4. Get the codomain curve E_(i+1) and dual isogeny phii_dual
    coE = phi_compI.codomain_curve
    phi_compI_dual = phi_compI.dual_isogeny()
    print("[INFO] E%d :"%(step), coE)

    # 4-1. Adjust the error [-1]
    T = phi_compI_dual.codomain_P
    ellT = phi_compI.eval(T)
    if ellT != phi_compI.degree * phi_compI_dual.domain_P:
        phi_compI_dual.codomain_P *= -1
        phi_compI_dual.codomain_Q *= -1
        assert -ellT == phi_compI.degree * phi_compI_dual.domain_P
    else: assert ellT == phi_compI.degree * phi_compI_dual.domain_P

    T = phi_compI.codomain_P
    ellT = phi_compI_dual.eval(T)
    assert ellT == phi_compI_dual.degree * phi_compI.domain_P
    isog_chain.append_forward(phi_compI)
    isog_dual_chain.append_backward(phi_compI_dual)

# # 1. Compute the right order O2
# O2 = I2.right_order()

# # 2. Extract the next ideal factor
# I3 = I2.conjugate() * I1.conjugate() * I
# I3 = I3.scale(1/ell^2)
# ellO2 = QA.ideal(O2.basis()).scale(ell)
# I3 = AddIdeal(I3, ellO2)

# assert(I3.norm() == ell and I3.left_order() == O2)

# isog2 = IsogenyChain([phi1, phi2])
# isog2_dual = IsogenyChain([phi2_dual, phi1_dual])

# # 3. Compute Corresponding isogeny
# try:
#     phi3_kernel_generator = IdealToIsogenySmall(I3, ell, isog2, isog2_dual, 148, 16)
#     print("[INFO] I3 to phi3 succeed")
# except Exception as e:
#     print("[ERROR] I3 to phi3 failed", e)
#     exit(0)
# phi3 = Isogeny(phi2.codomain_coeff, phi3_kernel_generator, 2^e1*3^e2*ell)

# # 4. Get the codomain curve E_3 and dual isogeny phi3_dual
# E3 = phi3.codomain_curve
# phi3_dual = phi3.dual_isogeny()
# print("E3 :", E3)