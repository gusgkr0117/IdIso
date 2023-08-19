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