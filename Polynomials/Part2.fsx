(* Part 2: Functional decomposition *)
#time
#load "Part1.fsx";;
open Part1
(** For uniqe representation of a polynomial we should have 
        [1;2;-3] = [1;2;-3;0;0] holds
    But in F# it is not.
    Therefore, when we consider the model of polynomial is legal only if 
        legal(LIST) if LIST=[]
    or  legal(LIST) if lastElement(LIST)<>0
**)
(** isLegal: int list -> bool 
The function isLegal tests whether an integer list is a legal representation of a polynomial.
let rec reverseList = function
    | [] -> []
    | x::XT -> let NXS = reverseList XT
               NXS @ [x];;
let rec reverseList1 ys = function
    | [] -> ys
    | x::XT -> reverseList1 x::ys XT
let isLegal XS = 
    match reverseList(XS) with
    | [] -> true
    | x::_ -> x<>0;;
isLegal [1;2;-3;0];;
**)
(** Better method **)
let rec isLegal = function
    | [] -> true
    | [x] -> x<>0 
    | _::XT -> let P = isLegal XT
               P && true;;
isLegal [0;1;2;-3;0;1;0;0];

(** prune: int list -> Poly 
Any integer list can be turned into a leagal representation of a polynomial by removal of 0's 
occurring at the end of the list. The function prune should do this.
let pred0 x = x=0;;

let rec reverseList1 YS = function
    | [] -> YS
    | x::XT -> reverseList1 (x::YS) XT;;
let reverseList XS = reverseList1 [] XS;;

let rec pruneH p = function
    | [] -> []
    | x::XT -> let NXS = pruneH p XT
               if p(x) then NXS else x::NXS
let prune XS = reverseList (pruneH pred0 (reverseList XS));;
prune [0;1;2;-3;0;1;0;0];;
**)

(** Better method 
reversing a list, home-made may not better than library one, so we can use List.rev for the task
**)
let pred0 x = x=0;;
let rec pruneH p XS = 
    match XS with
    | [] -> []
    | x::XT -> if p(x) then pruneH p XT else List.rev XS
let prune XS :Poly = pruneH pred0 (List.rev XS)  ;;

(** toString: Poly -> string 
Choose an appealing textual representation of a polynomial and declare an associated toString funciton. The output should be as follows:
    i.e. 1 - 3x^2 
means a polynomial which we modeled as integer list [1;0;-3]
    i.e. 0 
means empty list
Here we have to model the order of the polynomial.
**)

let rec fTerm f = function
    | (_,[]) -> ""
    | (o,x::XT) -> let cxo = fTerm f (o+1,XT)
                   f(o,x) + cxo;;
     
let fCx(o,x) = 
    match x with
    | 0 -> ""
    | n -> if n>0 then " + " + (string n) + "x^" + (string o)
           else " - " + (string -n) + "x^" + (string o);;
let toString (XS:Poly) = 
    match XS with
    | [] -> "0"
    | x::XT -> (string x) + fTerm fCx (1,XT);;
                       

toString [2;0;-3];;


(* derivative: Poly -> Poly 
For a polynomial P(x) = a_0 + a_1*x + a_2*x^2 + ... + a_n*x^n, we have 
    P'(x) = a_1 + 2a_2x + ... + n*a_n*x^n-1
*)
let rec derivativeH(o,XS) =
    match XS with
    | [] -> []
    | x::XT -> let NXS = derivativeH(o+1,XT)
               (x*o)::NXS;;
let derivative (XS:Poly) = 
    match XS with
    | [] -> []
    | x::XT -> derivativeH(1,XT) ;;
derivative [1;2;3;4];;

(** compose: Poly -> Poly -> Poly 
(P*Q)(x) = P(Q(x))
For instance, if P(x)=2+4x^3 and Q(x)=3x+2x^2 then
    2+4(3x+2x^2)^3 = 2 + 108x^3 + 216x^4 + 144x^5 + 32x^6
    compose [2;0;0;4] [0;3;2] = [2;0;0;108;216;144;31]
**)

let rec powerPp(o,XS) =
    match o with
    | 1 -> XS
    | _ -> let NXS = powerPp(o-1,XS)
           mul XS NXS;;
powerPp(3,[0;3;2])
mulC 4 (powerPp(3,[0;3;2]))
let rec composeH(o,XS) YS =
    match XS with
    | [] -> []
    | x::XT -> let NXS = composeH(o+1,XT) YS
               add (mulC x (powerPp(o,YS))) NXS;;
composeH(3,[4]) [0;3;2]

let compose XS YS = 
    match XS with
    | [] -> []
    | x::XT -> x::(composeH(1,XT) YS);;

compose [2;0;0;4] [0;3;2];;

