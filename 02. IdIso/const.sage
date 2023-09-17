# (p+1) = 2^148 * 5^2 * 127 * 347
# (p-1) = 2* 3^16 * 461 * 101359 * 1464289785449 * 66734777386835572730669
# p = 393108616061618412489735027422936257282820381081599
prime = 393108616061618412489735027422936257282820381081599
ell = 5
e1, e2 = 148, 16

QA.<QA_i,QA_j,QA_k> = QuaternionAlgebra(-1, -prime)
O0 = QA.quaternion_order([1, QA_i, QA_i/2+QA_j/2, QA_k/2+1/2])
K_temp.<x> = GF(prime)[]
Fp.<Fp2_i> = GF(prime^4, modulus = x^4 - 6*x^2 + 13, impl='pari_ffelt')
Fp_i = sqrt(Fp(-1))
E0 = EllipticCurve(Fp, [0, 0, 0, 1, 0])
E0_order = E0.gens()[0].order()