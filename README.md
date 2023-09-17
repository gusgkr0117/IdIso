# Implementation & Experiments for IdealToIsogeny
+ Converting an ideal to the corresponding isogeny via (2,2) and (3,3) isogenies
## Components
+ `(2,2)-isogeny`
    + Use Richelot isogeny
    + Sage implementation : [Castryk-Decru-SageMath](https://github.com/GiacomoPope/Castryck-Decru-SageMath.git)
    + Paper : [A note on reimplementing the Castryk-Decru attack and lessons learned for SageMath](https://eprint.iacr.org/2022/1283)
+ `(3,3)-isogeny`
    + Use [(3,3)-isogeny formulae by Bruine, Flynn and Testa(BFT)](https://eudml.org/doc/279018)
    + Magma implementation : [3_3_isogenies](https://github.com/KULeuven-COSIC/3_3_isogenies.git)
+ `Arithmetics in Quaternion algebra`
    + Use [the arithemetics in quaternion algebra in SageMath](https://doc.sagemath.org/html/en/reference/quat_algebras/sage/algebras/quatalg/quaternion_algebra.html)
## Parameters
+ The prime must be chosen to have as its factor $2^{e_1}$ and $3^{e_2}$
## Auxiliary Implementation of Arithmetics
+ The `order` method which calculates the order of the given elliptic curve point is too slow.
→ We are not to use `order` method. Most of the order of the points we use can be deduced.  
+ The `gens` method which outputs the basis of the elliptic curve group is too slow. Use the following instead.
→ `gen` method also has the issue that the pair of the points are not guaranteed to be independent. 
```python
E = EllipticCurve(Fp, [0, 0, 0, 1, 0])
P, Q = get_basis(E, N)
```