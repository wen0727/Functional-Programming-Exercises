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
(** Other method **)
let rec reverseList = function
    | [] -> []
    | X::tt -> let NXS = reverseList tt
               NXS @ [X];;
let rec reverseList1 ts = function
    | [] -> ts
    | X::st -> reverseList1 X::ts st
let reverseList ts = reverseList1 [] ts;;
let isLegal ts = 
    match reverseList(ts) with
    | [] -> true
    | X::_ -> X<>0;;
isLegal [1;2;-3;0];;
**)
(** Better method **)
let rec isLegal = function
    | [] -> true
    | [X] -> X<>0 
    | _::tt -> isLegal tt;;
isLegal [0;1;2;-3;0;1;0;0];

(** prune: int list -> Poly 
Any integer list can be turned into a leagal representation of a polynomial by removal of 0's 
occurring at the end of the list. The function prune should do this.
**)

(**A method 
reversing a list, home-made may not better than library one, so we can use List.rev for the task
let rec pruneH ts = 
    match ts with
    | [] -> []
    | X::tt -> if X=0 then pruneH tt else List.rev ts
let prune ts = pruneH (List.rev ts);;
List.rev [-2; 1; 0]
prune [-2; 1; 0]
**)

(** toString: Poly -> string 
Choose an appealing textual representation of a polynomial and declare an associated toString funciton. The output should be as follows:
    i.e. 1 - 3x^2 
means a polynomial which we modeled as integer list [1;0;-3]
    i.e. 0 
means empty list
Here we have to model the order of the polynomial.
**)

let rec pExp2str f = function
    | (_,[]) -> ""
    | (o,X::tt) -> let NS = pExp2str f (o+1,tt)
                   f(o,X) + NS;;
     
let pTerm2str(o,t) = 
    match t with
    | 0 -> ""
    | X -> if X>0 then " + " + (string X) + "x^" + (string o)
           else " - " + (string -X) + "x^" + (string o);;
let toString (ts:Poly) = 
    match ts with
    | [] -> "0"
    | X::tt -> (string X) + pExp2str pTerm2str (1,tt);;
                       
toString [2;0;-3];;


(* derivative: Poly -> Poly 
For a polynomial P(x) = a_0 + a_1*x + a_2*x^2 + ... + a_n*x^n, we have 
    P'(x) = a_1 + 2a_2x + ... + n*a_n*x^n-1
*)

let rec derivativeH = function
    | (_,[]) -> []
    | (0,ps) -> ps
    | (n,X::pt) -> let Nts = derivativeH(n+1,pt)
                   (X*n)::Nts;;
let derivative ts = derivativeH(0,ts);;
derivative [0;1;0];;
(** compose: Poly -> Poly -> Poly 
(P*Q)(x) = P(Q(x))
For instance, if P(x)=2+4x^3 and Q(x)=3x+2x^2 then
    2+4(3x+2x^2)^3 = 2 + 108x^3 + 216x^4 + 144x^5 + 32x^6

**)

let rec powerP ps = function
    | 0 -> [1]
    | n -> let NP = powerP ps (n-1)
           mul ps NP
mul [] [1];;

let rec fPsubst ps n qs =
    match ps with
    | [] -> []
    | X::pt -> let NP = fPsubst pt (n+1) qs
               add (mulC X (powerP qs n)) NP
   
let compose ps qs = fPsubst ps 0 qs;;
compose [2;0;0;4] [0;3;2];;
mul [2;0;0;4] [0;3;2];;
powerP (prune [0;0;1;0;0]) 3;;

fPsubst (prune [0;0;1;0;0]) 2 (prune [0;0;1;0;0]);;

compose [0;1] [];;
compose [0;1] [2;0;0;4];;
compose [2;0;0;4] [0;1];;
