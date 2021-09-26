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
(* Other method *)
let p0 t = t=0;;

let rec reverseList1 ts = function
    | [] -> ts
    | X::st -> reverseList1 (X::ts) st;;
let reverseList ts = reverseList1 [] ts;;

let rec pruneH p = function
    | [] -> []
    | X::tt -> let NXS = pruneH p tt
               if p(X) then NXS else X::NXS
let prune ts = reverseList (pruneH p0 (reverseList ts));;
prune [0;1;2;-3;0;1;0;0];;
**)

(** Better method 
reversing a list, home-made may not better than library one, so we can use List.rev for the task
**)
let rec pruneH ts = 
    match ts with
    | [] -> []
    | X::tt -> if X=0 then pruneH tt else List.rev ts
let prune ts = pruneH (List.rev ts);;
List.rev [-2; 1; 0]
prune [-2; 1; 0]
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
let rec derivativeH(o,ts) =
    match ts with
    | [] -> []
    | X::tt -> let Nts = derivativeH(o+1,tt)
               (X*o)::Nts;;
let derivative (ts:Poly) = 
    match ts with
    | [] -> []
    | X::tt -> derivativeH(1,tt) ;;
    derivative [1;2;3;4];;
*)
let rec derivativeH(o,ts) =
    match ts with
    | [] -> []
    | X::tt -> let Nts = derivativeH(o+1,tt)
               if o=0 
               then Nts 
               else (X*o)::Nts;;
let derivative (ts:Poly) = derivativeH(0,ts) ;;
derivative [1;2;3;4];;

(** compose: Poly -> Poly -> Poly 
(P*Q)(x) = P(Q(x))
For instance, if P(x)=2+4x^3 and Q(x)=3x+2x^2 then
    2+4(3x+2x^2)^3 = 2 + 108x^3 + 216x^4 + 144x^5 + 32x^6
    compose [2;0;0;4] [0;3;2] = [2;0;0;108;216;144;31]
(* Other method *)
let rec powerP(o,ts) =
    match o with
    | 1 -> ts
    | _ -> let Nts = powerP(o-1,ts)
           mul ts Nts;;
powerP(3,[0;3;2])
mulC 4 (powerPp(3,[0;3;2]))
let rec composeH(o,ss) ts =
    match ss with
    | [] -> []
    | X::st -> let Nss = composeH(o+1,st) ts
               add (mulC X (powerP(o,ts))) Nss;;
composeH(3,[4]) [0;3;2]

let compose ss ts = 
    match ss with
    | [] -> []
    | X::st -> x::(composeH(1,st) ts);;
compose [2;0;0;4] [0;3;2];;
**)
let rec powerP(o,ts) =
    match o with
    | 0 -> [1]
    | 1 -> ts
    | _ -> let Nts = powerP(o-1,ts)
           if o>0
           then mul ts Nts
           else failwith "The function does not support negative exponent.";;
powerP(3,[0;3;2])
mulC 4 (powerP(3,[0;3;2]))
let rec pSubst(o,ss) ts =
    match ss with
    | [] -> []
    | X::st -> let Nss = pSubst(o+1,st) ts
               if o=0
               then add [X] Nss
               else add (mulC X (powerP(o,ts))) Nss;;
pSubst(3,[4]) [0;3;2]

let compose ss ts = pSubst(0,ss) ts;;
compose [2;0;0;4] [0;3;2];;

