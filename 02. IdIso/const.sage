# (p+1) = 2^18 * 5
prime = 1310719
ell = 5

QA.<QA_i,QA_j,QA_k> = QuaternionAlgebra(-1, -prime)
O0 = QA.quaternion_order([1, QA_i, QA_i/2+QA_j/2, QA_k/2+1/2])
K_temp.<x> = GF(prime)[]
Fp.<Fp2_i> = GF(prime^4, modulus = x^4 + 20*x^2 + 101)
Fp_i = sqrt(Fp(-1))
E0 = EllipticCurve(Fp, [0, 0, 0, 1, 0])
E0_oder = E0.gens()[0].order()