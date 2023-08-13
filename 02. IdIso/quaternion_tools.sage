import random
load('const.sage')

def ideal_generator(ideal):
    norm = ideal.norm()
    basis = ideal.basis()

    left_order = ideal.left_order()
    left_order_norm = QA.ideal(left_order.basis()).scale(norm)
    for i in range(4):
        if not IdealContains(left_order_norm, basis[i]): return basis[i]

def AddIdeal(I1, I2):
    return QA.ideal(basis_for_quaternion_lattice(list(I1.basis()) + list(I2.basis())))

def IdealContains(L, a):
    A1 = QA.ideal(O0.basis()).scale(a, left=False)
    # print([L.basis()[j] - basis_for_quaternion_lattice(L.basis() + A1.basis())[j] for j in range(4)])
    return [L.basis()[j] - basis_for_quaternion_lattice(L.basis() + A1.basis())[j] for j in range(4)] == [0,0,0,0]

def GetRandomIdealElle(e=6):
    L0 = QA.ideal(O0.basis())
    O2 = QA.ideal(O0.basis()).scale(ell)
    for ei in range(e):
        basis= L0.basis()
        while True:
            v = [random.randint(-1000,1000) for i in range(4)]
            alpha = v[0] * basis[0] + v[1] * basis[1] + v[2] * basis[2] + v[3] * basis[3]
            if (Integer(alpha.reduced_norm()) % (ell^(ei+1))) !=0: continue
            if not IdealContains(O2, alpha): break
        
        L1 = QA.ideal(O0.basis()).scale(alpha, left=False)
        L2 = QA.ideal(O0.basis()).scale(ell^(ei + 1), left=False)
        L0 = AddIdeal(L1, L2)
        
    return L0

def O0IdealToIsogeny(I):
    #TODO
    return 0

def GetReducedBasis(basis):
    basis = matrix([a.coefficient_tuple() for a in basis])
    
    O_gram = matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, prime, 0], [0, 0, 0, prime]])
    gram = basis * O_gram * basis.transpose()

    T = gp.qflllgram(gram)
    T_sage = [[0 for i in range(4)] for _ in range(4)]
    for i1 in range(4):
        for i2 in range(4):
            T_sage[i1][i2] = Integer(gp(T[i1+1,i2+1]))
    T = matrix(T_sage)
    reduced_basis = (basis.transpose() * T).transpose()
    reduced_basis = [QA(x) for x in reduced_basis]
    return reduced_basis

def GetCoeff(O_):
    B1 = [vector(v.coefficient_tuple()) for v in O_.basis()]
    B0 = [vector(v.coefficient_tuple()) for v in O0.basis()]
    B1 = matrix(B1)
    B0 = matrix(B0)
    return B1 * B0.inverse() * ell

def O0_coordinate(x) :
    assert x in O0, "x is not in O0"
    x_vector = vector(x.coefficient_tuple())
    O0_basis = [v.coefficient_tuple() for v in O0.basis()]
    M = matrix(O0_basis)
    return (x_vector * M)