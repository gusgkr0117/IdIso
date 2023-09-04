import sys
from random import randint


def find_prime(n, ell):
    d = 6

    while True:
        two_factor = 2 ^ n
        print("n:", n)
        f = ((two_factor * ell) % 3) * 2
        p = 0
        max_3 = 0
        f_len = floor(log(f, 2))
        p = two_factor * ell * f - 1
        while (ell ^ 2 * f) ^ d < p:
            f = f + 3

            # if f_len != floor(log(f, 2)):
            #     print(f, f_len)
            #     f_len = floor(log(f, 2))

            p = two_factor * ell * f - 1

            # if max_3 < (p-1).valuation(3):
            #     max_3 = (p-1).valuation(3)
            #     print("max of val_3 :", max_3)
            #     print(3 ^ ((p-1).valuation(3)), ell ^ 2 * f)

            if 3 ^ ((p-1).valuation(3)) < ell ^ 2 * f:
                continue
            if p.is_prime():
                print("found! :", p)
                return p
                break
            print(p, "is not prime")
        n = n + 1
