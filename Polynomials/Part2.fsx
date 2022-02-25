(* Part 2: Functional decomposition *)

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
**)
let rec isLegal (xs : Poly) = 
    match xs with
    | [] -> true
    | [X] -> X<>0 
    | _::xt -> isLegal xt;;
isLegal [0;1;2;-3;0;1;0;0];;

(** prune: int list -> Poly 
Any integer list can be turned into a leagal representation of a polynomial by removal of 0's 
occurring at the end of the list. The function prune should do this.
**)

let rec fRemove0 xs = 
    match xs with
    | [] -> []
    | x::xt -> if x=0 
               then fRemove0 xt
               else List.rev xs;;
let prune xs : Poly = fRemove0 (List.rev xs);;

(** toString: Poly -> string 
Choose an appealing textual representation of a polynomial and declare an associated toString funciton. The output should be as follows:
    i.e. 1 - 3x^2 
means a polynomial which we modeled as integer list [1;0;-3]
    i.e. 0 
means empty list
Here we have to model the order of the polynomial.
**)

let fXorder =
    function
    | 0 -> ""
    | 1 -> "x"
    | n -> "x^"+ string n;;

let fTerm n = 
    function
    | 0 -> ""
    | 1 -> "+" + fXorder n 
    | c -> if c>1 then "+" + string c + fXorder n
           else string c + fXorder n

let rec fPRterm n = 
    function
    | [] -> ""
    | x::xt -> fTerm n x + fPRterm (n+1) xt;;
let rec fPFterm n = 
    function
    | [] -> ""
    | x::xt when x<>0 -> string x + fXorder n + fPRterm (n+1) xt
    | _::xt -> fPFterm (n+1) xt;;

let toString ts = fPFterm 0 ts;;
toString [0;0;0;2]
toString [1;1;0;-3;6;8;10]

(* derivative: Poly -> Poly 
For a polynomial P(x) = a_0 + a_1*x + a_2*x^2 + ... + a_n*x^n, we have 
    P'(x) = a_1 + 2a_2x + ... + n*a_n*x^n-1
*)

let rec derivativeH = 
    function
    | (_,[]) -> []
    | (n,x::xt) -> let NT = derivativeH(n+1,xt)
                   if n=0 then derivativeH(n+1,xt)
                   else (x*n)::NT;;
let derivative ts = derivativeH(0,ts);;
derivative [0;1;0];;
(** compose: Poly -> Poly -> Poly 
(P*Q)(x) = P(Q(x))
For instance, if P(x)=2+4x^3 and Q(x)=3x+2x^2 then
    2+4(3x+2x^2)^3 = 2 + 108x^3 + 216x^4 + 144x^5 + 32x^6

**)

let rec powerP ps = 
    function
    | 0 -> [1]
    | n -> let NP = powerP ps (n-1)
           mul ps NP
mul [] [1];;

let rec fPsubst ps n qs =
    match ps with
    | [] -> []
    | X::pt -> let NP = fPsubst pt (n+1) qs
               add (mulC X (powerP qs n)) NP
   
let compose (ps : Poly) (qs : Poly) : Poly = fPsubst ps 0 qs;;
compose [2;0;0;4] [0;3;2];;
mul [2;0;0;4] [0;3;2];;
powerP (prune [0;0;1;0;0]) 3;;

fPsubst (prune [0;0;1;0;0]) 2 (prune [0;0;1;0;0]);;

compose [0;1] [];;
compose [0;1] [2;0;0;4];;
compose [2;0;0;4] [0;1];;
