(* Part 5: Correctness - property-based testing *)
#load "Part1.fsx"
#load "Part2.fsx"
#load "Part3.fsx"
#load "Part4.fsx"
#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"

open Part1
open Part2
open Part3
open Part4
open FsCheck

(** Exploit the prune function to generates legal representation of polynomials. **)
let addInv p1 p2 = isLegal(add (prune p1) (prune p2));;
let _ = Check.Quick addInv;;

(** Property-test of the isLegal ivariant for the functions in Part 1,
        add: Poly -> Poly -> Poly   not ok
        mulC: int -> Poly -> Poly   ok
        sub: Poly -> Poly -> Poly   not ok
        mulX: Poly -> Poly          ok
        mul: Poly -> Poly -> Poly   ok
**)
let mulCInv n ps = isLegal(mulC n (prune ps));;
let _ = Check.Quick mulCInv;;

let subInv ps qs = isLegal(sub (prune ps) (prune qs));;
let _ = Check.Quick subInv;;

let mulXInv ps = isLegal(mulX (prune ps));;
let _ = Check.Quick mulXInv;;

let mulInv ps qs = isLegal(mul (prune ps) (prune qs));;
let _ = Check.Quick mulInv

(** Property-test of the isLegal ivariant for the functions in Part 2,
    prune: int list -> Poly         ok
    derivative: Poly -> Poly        not ok
    compose: Poly -> Poly -> Poly   ok
**)

let pruneInv ps = isLegal(prune ps);;
let _ = Check.Quick pruneInv;;

let derivativeInv ps = isLegal(derivative (prune ps));;
let _ = Check.Quick derivativeInv;;

(* Comment: unknown length * 100 test length is too much for this implementation. *)
//let composeInv ps qs = isLegal(compose (prune ps) (prune qs));;
//let _ = Check.Quick composeInv;;


(** Property of a commutative ring 
    1. give F# declaration for add identity Zero, mul identity One and the add inverse -.
    2. check the properties 1. - 9. using property-based testing.
**)
let Zero = [];;
let One = [1];;
let fPaddInv p = sub Zero p;;



(*** 1. For all p1,p2 and p3:
    (p1 + p2) + p3 = p1 + (p2 + p3)
add is associative 
***)
let addAssoc p1 p2 p3 = 
    add (add p1 p2) p3 = add p1 (add p2 p3);;
let _ = Check.Quick addAssoc;;

(*** 2. For all p1 and p2:
    p1 + p2 = p2 + p1
add is commutative
***)
let addCommut p1 p2 = 
    add p1 p2 = add p2 p1;;
let _ = Check.Quick addCommut;;

(*** 3. For all p:
    p + identity = p = identity + p
additive identity
***)
let addId p = 
    add p Zero = (prune p) && 
        (prune p) = add Zero p;;
(*comment: this also includes the commutative property *)
let _ = Check.Quick addId;;

(*** 4. For all p:
    p + (-p) = identity
-p is called the additive inverse of p
***)
let addInver p = 
    add p (fPaddInv p) = Zero;;
let _ = Check.Quick addInver;;

(*** 5. For all p1, p2 and p3:
    (p1 p2) p3 = p1 (p2 p3)
mul is associative
***)
let mulAssoc p1 p2 p3 =
    mul (mul p1 p2) p3 =
        mul p1 (mul p2 p3);;
let _ = Check.Quick mulAssoc;;

(*** 6. For all p1 and p2: 
    p1 p2 = p2 p1
mul is commutative
***)
let mulCommu p1 p2 = 
    mul p1 p2 = 
        mul p2 p1;;
let _ = Check.Quick mulCommu;;

(*** 7. There is a polynomial multiplicative identity so that for all p:
 p [1] = p = [1] p    
***)
let mulId p =
    mul p One = (prune p) &&
        (prune p) = mul One p;;
let _ = Check.Quick mulId;; 

(*** 8 and 9 For all p1,p2,p3:
    p1 (p2 + p3) = p1 p2 + p1 p3
    (p1 + p2)p3 = p1 p3 + p2p3
multiplication is distributive
***)
let mulDistr8 p1 p2 p3 =
    mul p1 (add p2 p3) =
        add (mul p1 p2) (mul p1 p3);;
let _ = Check.Quick mulDistr8;;

let mulDistr9 p1 p2 p3 = 
    mul (add p1 p2) p3 =
        add (mul p1 p3) (mul p2 p3);;
let _ = Check.Quick mulDistr9;;

(*** Associative property for polynomial functions 
    add, mul and compose, appeared in 1, 5 and 10 can be declared with high-order funciton
to avoid repetitions of the prediction such as follows.
***)
let assoc f p1 p2 p3 = 
    f (f p1 p2) p3 =
        f p1 (f p2 p3);;
(*** Then we can just substitute either add,mul or compose to "f" to test the associative prorerty of the function.
***)

let addPAssoc p1 p2 p3 = 
    assoc add p1 p2 p3;; 
let _ = Check.Quick addPAssoc;;

let mulPAssoc p1 p2 p3 = 
    assoc mul p1 p2 p3;;
let _ = Check.Quick mulPAssoc;;

//let composePAssoc p1 p2 p3 = 
//    assoc compose p1 p2 p3;;
//let _ = Check.Quick composePAssoc;;

(**** Associative property can be defined as an infix operator.
Details can be find out how to do it in section 2.9 in HR book.
****)

(*** Monoid, if the polynomial(set) satisfies two properties(axioms)
Those are associativity and the identity element. Properties such as 
    1(add assoc) and 3(add id) 
    5(mul assoc) and 6(mul id)
    10(compose assoc) and 11(compose id)
shows add,mul and compose are the submonoid binary operation. So we can 
declare a monoid property for polynomials operations.
***)

(** 3. give an F# declaration for Id and test property 11. 
    4. try to test property 10 with Check.Quick and experience the problems.
       Make a better control on the input polynomials i.e. number of the element,
       tests i.e. number of tests. See Appendix C.
**)

(*** 10. For all p1,p2 and p3:
    (p1 o p2) o p3 = p1 o (p2 o p3)            --- o means compose here
(* Comment, does not work. Refer to page 10 line 7 in Polynomial exercise. *)
let composeAssoc p1 p2 p3 =
    compose (compose p1 p2) p3 = 
        compose p1 (compose p2 p3);;
let _ = Check.Quick composeAssoc;;
***)

(*** Appendix C, controlled FsCheck. ***)
let composeAssoc en tn =
    let gen = FsCheck.Arb.generate<int list>
    let gen3 = Gen.three gen
    let operands = Gen.sample en tn gen3
    let prop (l1,l2,l3) = 
        let p1 = prune l1
        let p2 = prune l2
        let p3 =  prune l3
        assoc compose p1 p2 p3
        //pAssoci po1 po2 po3 compose
    (operands, List.forall prop operands);;
composeAssoc 10 100;;

(*** 11. There is a polynomial Id so that for all p 
    p  o Id = p and Id o p = p
***)
let Id = [0;1]
let composeId p q = 
    compose p Id = (prune p) &&
    compose Id p = (prune p);;
let _ = Check.Quick composeId;;

(** Properties of structure-preserving functions 
        for eval and degree functions.
        h_k denote the function: eval k: Poly -> int
        h_k is called a homomorphism in algebra. It is a structure-preserving function,
        from the type Poly with its operations to the algebra of integers.
        
**)
(*** 12. For all k, p1 p2:
        h_k(add p1 p2) = h_k(p1) + h_k(p2)
***)
let h_kAdd p1 p2 k = 
    eval k (add p1 p2) = (eval k p1) + (eval k p2) ;;
let _ = Check.Quick h_kAdd;;
(*** 13. For all k, p1 p2:
    h_k(mul p1 p2) = h_k(p1) h_k(p2)
***)
let h_kMul p1 p2 k = 
    eval k (mul p1 p2) = (eval k p1) * (eval k p2) ;;
let _ = Check.Quick h_kMul;;

(*** 14. For all p1 and p2:
    the degree of two polynomials' addition should less or equal to 
    maximum degree between p1 and p2
***)
let h_oAdd p1 p2= 
    degree(add p1 p2) <= max (degree p1) (degree p2);;
let _ = Check.Quick h_oAdd;;

(*** 15. For all p1 and p2:
    the degree of two polynomials' multiplication should less or equal to 
    maximum degree between p1 and p2
***)

let h_oMul p1 p2 =
    degree(mul p1 p2) = addD (degree (prune p1)) (degree (prune p2));;
let _ = Check.Quick h_oMul;;

(**** find a counter-example for the property
        degree(add p1 p2) = max (degree p1) (degree p2)
****)
degree(add [0;1;2;3] [0;1;2;-3]) = max (degree [0;1;2;3]) (degree [0;1;2;-3])