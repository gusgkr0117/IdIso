import random, copy
load('const.sage')
load('quaternion_tools.sage')
load('isogeny.sage')
load('../01. jacobian_isogeny/22_isogeny.sage')
load('../01. jacobian_isogeny/33_isogeny.sage')

def cornacchia(d, m):
    try: 
        (x,y) = DiagonalQuadraticForm(QQ, [1,d]).solve(m)
        if not x.is_integer() or not y.is_integer() :
            print(x,y)
            raise Exception("No solution")
        return x, y
    except: raise Exception("No solution")

def cornacchia_custom(d, m):
    assert kronecker(-d, m) == 1
    r0 = Integer(sqrt(mod(-d, m)))
    if r0 < m/2: r0 = m - r0
    r1 = m % r0
    while r1 > floor(sqrt(m)):
        r2 = r0 % r1
        r1, r0 = r2, r1
    if not Integer((m-r1^2)/d).is_square(): return None
    x,y = r1, Integer(sqrt((m-r1^2)/d))
    assert x^2 + d*y^2 == m
    return x,y


# def GetAlphaBeta(I, N, O_basis):
#     print("I :", I)
#     I_basis = GetReducedBasis(I.basis())
#     O_ell = QA.ideal(O_basis).scale(I.norm())
#     I_generator = None
#     for i in range(4):
#         if not IdealContains(O_ell, I_basis[i]):
#             I_generator = I_basis[i]
#             break

#     assert I_generator != None, "There must be a generator"

#     gram = matrix([[1,0,0,0],[0,1,0,0],[0,0,prime,0],[0,0,0,prime]])
#     M_O = matrix([vector(v.coefficient_tuple()) for v in O_basis])
#     G = M_O * gram * M_O.transpose()

#     x,y = 0, 0
#     k = floor(sqrt(prime))
#     beta = None
#     # The random multiplication by 1 or 2 to I_generator is needed to cover all parity of n(alpha)
#     for i in range(100*k^2):
#         alpha = random.randint(1,5)*I_generator + random.randint(-k, k) * I_basis[1] + random.randint(-k, k) * I_basis[0]
#         if gcd(alpha.reduced_norm(), N) != 1: continue
#         target = N - alpha.reduced_norm()
#         if not target > 0 : continue
#         if kronecker(-G[1][1], target) != 1: continue
#         try:
#             x,y = cornacchia_custom(G[1][1], target)
#             beta = O_basis[0]*x + O_basis[1]*y
#             break
#         except Exception as e:
#             print(e)
#             print("no solution for", G[1][1], target)
#             continue
    
#     if beta == None: breakpoint()
    
#     assert (beta.reduced_norm() + alpha.reduced_norm()) == N, "n(beta) + n(alpha) = N"
#     assert gcd(beta.reduced_norm(), alpha.reduced_norm()) == 1, "gcd(n(beta), n(alpha)) = 1"
#     tempI = QA.ideal(O_basis).scale(alpha, left=False)
#     assert GetReducedBasis(AddIdeal(tempI, O_ell).basis()) == I_basis, "The generator is wrong"
#     return alpha, beta

def GetAlphaBeta(I, N):
    print("I :", I)
    O0_basis = GetReducedBasis(O0.basis())
    O_basis = GetReducedBasis(I.left_order().basis())
    I_basis = GetReducedBasis(I.basis())
    O_ell = QA.ideal(O_basis).scale(I.norm())
    I_generator = None
    for i in range(4):
        if not IdealContains(O_ell, I_basis[i]):
            I_generator = I_basis[i]
            break

    assert I_generator != None, "There must be a generator"

    gram = matrix([[1,0,0,0],[0,1,0,0],[0,0,prime,0],[0,0,0,prime]])
    M_O = matrix([vector(v.coefficient_tuple()) for v in O0_basis])
    G = M_O * gram * M_O.transpose()

    x,y = 0, 0
    k = floor(sqrt(prime))
    beta = None
    # The random multiplication by 1 or 2 to I_generator is needed to cover all parity of n(alpha)
    for i in range(100*k^2):
        alpha = random.randint(1,4)*I_generator + random.randint(-k, k) * I_basis[1] + random.randint(-k, k) * I_basis[0]
        if gcd(alpha.reduced_norm(), N) != 1: continue
        target = N - alpha.reduced_norm()
        if not target > 0 : continue
        if kronecker(-G[1][1], target) != 1: continue
        try:
            x,y = cornacchia_custom(G[1][1], target)
            beta = O0_basis[0]*x + O0_basis[1]*y
            break
        except Exception as e:
            continue
    
    if beta == None: breakpoint()
    
    assert (beta.reduced_norm() + alpha.reduced_norm()) == N, "n(beta) + n(alpha) = N"
    assert gcd(beta.reduced_norm(), alpha.reduced_norm()) == 1, "gcd(n(beta), n(alpha)) = 1"
    tempI = QA.ideal(O_basis).scale(alpha, left=False)
    assert GetReducedBasis(AddIdeal(tempI, O_ell).basis()) == I_basis, "The generator is wrong"
    return alpha, beta

def IdealToIsogenySmall(I, ell, isoChain, isoChainDual, e1, e2):
    assert I.norm() == ell
    O_left = I.left_order()
    E_domain = isoChain.codomain_curve
    O_left_basis = GetReducedBasis(O_left.basis())

    N = 2^e1*3^e2

    while True:
        # Computing alpha and beta
        alpha, beta = GetAlphaBeta(I, N)
        assert IdealContains(I, alpha), "alpha is not contained in the ideal"
        assert IdealContains(QA.ideal(O0.basis()), beta), "beta is not contained in the ideal"

        if not IdealContains(QA.ideal(O_left_basis), beta):
            print("beta is not contained in O_left")
        else: continue

        print("alpha :", alpha)
        print("n(alpha) :", alpha.reduced_norm().factor())
        print("beta :", beta)
        print("n(beta) :", beta.reduced_norm().factor())

        # Computing x = n(beta)^-1 mod N
        N_alpha = alpha.reduced_norm()
        N_beta = beta.reduced_norm()
        x_value = Integer(mod(N_beta, N)^-1)
        # The n(alpha) and x must be coprime
        while gcd(N_alpha, x_value) != 1: x_value += N
        print("x_value found")

        # Get basis
        P, Q = get_basis(E_domain, N)

        # # Endomorphism TEST
        # testv1, testv2 = alpha, beta
        # test1_P = eval_endomorphism(testv1.conjugate(), P, N, isoChain, isoChainDual)
        # test1_P = eval_endomorphism(testv2*x_value, test1_P, N, isoChain, isoChainDual)
        # test2_P = eval_endomorphism(x_value*testv2*testv1.conjugate(), P, N, isoChain, isoChainDual)
        # assert test2_P == test1_P, "eval_endomorphism error!"

        # Evaluate the endomorphism
        psi_P = eval_endomorphism(x_value * beta * alpha.conjugate(), P, N, isoChain, isoChainDual)
        #psi_P = eval_endomorphism(beta, psi_P, N, isoChain, isoChainDual)
        psi_Q = eval_endomorphism(x_value * beta * alpha.conjugate(), Q, N, isoChain, isoChainDual)
        #psi_Q = eval_endomorphism(beta, psi_Q, N, isoChain, isoChainDual)

        [ell_P, ell_Q] = get_basis(E_domain, ell)

        # Check if the kernel is maximally isotropic
        points = [P, Q, psi_P, psi_Q]
        points = [E_domain((e[0], e[1])) for e in points]
        assert points[0].weil_pairing(points[1], N)*points[2].weil_pairing(points[3], N) == 1, "The kernel is not maximally isotropic"
        
        points = points + [ell_P, ell_Q]

        # load('../01. jacobian_isogeny/22_isogeny.sage')
        # Computing the (2,2) and (3,3) - isogenies between hyperelliptic curves
        ## 1. (2,2)-Gluing
        points = [(points[0], points[2]), (points[1], points[3]), (points[4], E_domain(0)), (points[5], E_domain(0))]
        kernel2 = [(3^e2*2^(e1-1)*D[0], 3^e2*2^(e1-1)*D[1]) for D in [points[0], points[1]]]
        try:
            h, points, isog = Gluing22(E_domain, E_domain, kernel2, eval_points = points)
        except Exception as e:
            print(e)
            print("choose alpha and beta again")
            continue
        break
    #print("after gluing :", h.absolute_igusa_invariants_kohel())

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
    coP, coQ = E_domain(0), E_domain(0)
    if prodE[0].j_invariant() == E_domain.j_invariant():
        coP, coQ = eval_points[0][0], eval_points[1][0]
    else:
        coP, coQ = eval_points[0][1], eval_points[1][1]

    # The codomain points have error of multiplication by -1
    # So, the point is actually not accurate
    # But the kernel is identical
    print(coP, coQ)
    assert (ell*coP).is_zero() and (ell*coQ).is_zero()
    assert coP.curve().j_invariant() == E_domain.j_invariant()
    assert coQ.curve().j_invariant() == E_domain.j_invariant()
    
    isomorph = coP.curve().isomorphism_to(E_domain)
    coP, coQ = isomorph(coP), isomorph(coQ)

    kernel = coP
    if coP.is_zero(): kernel = coQ

    return kernel

set_verbose(-1)
step_len = 9
# 1. Get Random Ideal of norm ell^e
I = GetRandomIdealElle(step_len)
assert(I.norm() == ell^step_len)
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
isog_list = [phi1]
isog_dual_list = [phi1_dual]
isog_chain = IsogenyChain([phi1])
isog_dual_chain = IsogenyChain([phi1_dual])
## Splitting TEST
test_case = 10
for case in range(test_case):
    # 1. Compute the right order O1
    prevO = I1.right_order()

    # 2. Extract the next ideal factor
    contI = I1.conjugate() * I
    contI = contI.scale(1/ell)
    ell_prevO = QA.ideal(prevO.basis()).scale(ell)
    compI = AddIdeal(contI, ell_prevO)

    assert compI.norm() == ell and compI.left_order() == prevO

    # 3. Compute Corresponding isogeny
    try:
        kernel_generator = IdealToIsogenySmall(compI, ell, isog_chain, isog_dual_chain, e1, e2)
        print("[INFO] I2 to phi2 succeed")
    except Exception as e:
        print("[ERROR] I2 to phi2 failed", e)
        continue
    
    phi_compI = Isogeny(isog_chain.chain[-1].codomain_coeff, kernel_generator, 2^e1*3^e2*ell)

    # 4. Get the codomain curve E_(i+1) and dual isogeny phii_dual
    coE = phi_compI.codomain_curve
    phi_compI_dual = phi_compI.dual_isogeny()
    print("[INFO] #%d E2 :"%(case), coE)
    print("[INFO] j-inv(E2) :", coE.j_invariant())

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

# for step in range(2, step_len + 1):
#     # 1. Compute the right order O1
#     prevO = compI.right_order()

#     # 2. Extract the next ideal factor
#     contI = compI.conjugate() * contI
#     contI = contI.scale(1/ell)
#     ell_prevO = QA.ideal(prevO.basis()).scale(ell)
#     compI = AddIdeal(contI, ell_prevO)

#     assert compI.norm() == ell and compI.left_order() == prevO

#     # 3. Compute Corresponding isogeny
#     try:
#         kernel_generator = IdealToIsogenySmall(compI, ell, isog_chain, isog_dual_chain, e1, e2)
#         print("[INFO] I%d to phi%d succeed"%(step, step))
#     except Exception as e:
#         print("[ERROR] I%d to phi%d failed"%(step, step), e)
#         raise Exception("stop")
    
#     phi_compI = Isogeny(isog_chain.chain[-1].codomain_coeff, kernel_generator, 2^e1*3^e2*ell)

#     # 4. Get the codomain curve E_(i+1) and dual isogeny phii_dual
#     coE = phi_compI.codomain_curve
#     phi_compI_dual = phi_compI.dual_isogeny()
#     print("[INFO] E%d :"%(step), coE)

#     # 4-1. Adjust the error [-1]
#     T = phi_compI_dual.codomain_P
#     ellT = phi_compI.eval(T)
#     if ellT != phi_compI.degree * phi_compI_dual.domain_P:
#         phi_compI_dual.codomain_P *= -1
#         phi_compI_dual.codomain_Q *= -1
#         assert -ellT == phi_compI.degree * phi_compI_dual.domain_P
#     else: assert ellT == phi_compI.degree * phi_compI_dual.domain_P

#     T = phi_compI.codomain_P
#     ellT = phi_compI_dual.eval(T)
#     assert ellT == phi_compI_dual.degree * phi_compI.domain_P
#     isog_list = isog_list + [phi_compI]
#     isog_dual_list = [phi_compI_dual] + isog_dual_list
#     isog_chain = IsogenyChain(isog_list)
#     isog_dual_chain = IsogenyChain(isog_dual_list)