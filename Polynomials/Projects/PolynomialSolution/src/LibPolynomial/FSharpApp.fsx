#I @"D:\General Repository\Functional-Programming-Exercises\Polynomials\Projects\PolynomialSolution\src\LibPolynomial\bin\Debug\net6.0"
#r @"LibPolynomial.dll"

open Polynomial
let p1 = ofList [1; 2];;
// val p1 : Polynomial.Poly = 1 + 2x
let p2 = ofList [3;4;5];;
p1 = p2
// val p2 : Poly = 3 + 4x + 5x^2
let p3 = ofList [0;0;0;0;2];;
// val p3 : Poly = 2x^4
let p4 = p1 + p2*p3;;
// val p4 : Poly = 1 + 2x + 6x^4 + 8x^5 + 10x^6
let p5 = compose p4 p3;;
// val p5 : Poly = 1 + 4x^4 + 96x^16 + 256x^20 + 640x^24
let p6 = derivative p5;;
degree (p4)
degree p4 = degree p6
degree p4 > degree p6
// val p6 : Poly = 16x^3 + 1536x^15 + 5120x^19 + 15360x^23
let d = max (degree p4) (degree p6);;
degree p4
degree p6
max (degree p4) (degree p6)
degree p4 = degree p6
// val d : Degree = Fin 23

