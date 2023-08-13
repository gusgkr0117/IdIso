import sys
from random import randint

if len(sys.argv) < 3 : exit()

n = int(sys.argv[1])
ell = int(sys.argv[2])

two_factor = 2^(floor(n))
f_len = floor(log(2^(floor(n))/ell,2))

p = 0
while True:
    f = randint(2^f_len, 2^(f_len + 1))
    p = two_factor * ell * f - 1
    if p.is_prime() : break

print(p)
print((p+1).factor())