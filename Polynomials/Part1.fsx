(* Mini-project: Computing with Polynomials *)
(** Part 1: Recursive list functions **)
(*** Type abbreviation, acronym ***)

type Poly = int list

(*** add: Poly -> Poly -> Poly 
Addition of two polynomials represented by lists is performed by element-wise additions. 
The order of the polynomials are represented by the order of the list. 
For instance, (1+2x)+(3+4x+5x^2+6x^3)=4+6x+5x^2+6x^3 is represented by
    add [1;2] [3;4;5;6] = [4;6;5;6]
***)

let rec add (ss : Poly) (ts : Poly) : Poly = 
    match (ss,ts) with
    | ([],_) -> ts
    | (_,[]) -> ss
    | (X::st,Y::tt) -> (X+Y)::add st tt;;
add [1;2] [3;4;5;6];;
(* For add ss ts, even ss and ts are assumed as legal representation of polynomials the new polynomial can be still illegal representation without prune function. 
For instance, add [-1] [1] would be illegal without applying prune function to the result. Same result would be seen in sub and compose function *)



(*** mulC: int -> Poly -> Poly *
The function mulC should implement the multiplication of a polynomial by a constant. For 
instance, 2(2+x^3)=4+2^3 and we represent this by
    mulC 2 [2;0;0;1] = [4;0;0;2]
**)
let rec mulC c (ts : Poly) : Poly =
    match ts with
    | _ when c=0 -> []
    | [] -> []
    | X::tt -> (c*X)::mulC c tt;; 
mulC 2 [2;0;0;1];;
mulC 2 [0];;
mulC 0 [1];;

(*** sub: Poly -> Poly -> Poly 
Subtraction of two polynomials represented by lists is performed by element-wise substrac
-tions. For instance, (1+2x)-(3+4x+5x^2+6x^3)=-2-2x-5x6^2-6x^3 and we represent this as 
follows:
    sub [1;2] [3;4;5;6] = [-2;-2;-5;-6]

let sub ps qs = add ps (mulC -1 qs)
***)
let rec sub (ss : Poly) (ts : Poly) :Poly =
    match (ss,ts) with
    | ([],Y::tt) -> -Y::sub [] tt
    | (_,[]) -> ss
    | (X::st,Y::tt) -> (X-Y)::sub st tt;;
sub [1;2] [3;4;5;6];;
sub [-1] [-1];;
(*** mulX: Poly -> Poly
The multiplication function mulX should implement the multiplication of a polynomial by  
x. For instance, x(2+x^3)=2x+x^4 and we represent that by
    mulX [2;0;0;1]=[0;2;0;0;1]
***)
let mulX (ts : Poly) : Poly =
    match ts with
    | [] -> []
    | _ -> 0::ts;;
mulX [2;0;0;1];;

(*** mul: Poly -> Poly -> Poly
Multiplication Properties
0Q(x)=0
(a_0+a_1x+...+a_nx^n)Q(x) =
    a_0Q(x)+x(a_1+a_2x+...+a_nx^n-1)Q(x)
For instance, (2+3x+x^3)(1+2x+3x^2)=2+7x+12^2+10x^3+2x^4+3x^5 and this can be represented 
as follows:
    mul [2;3;0;1] [1;2;3]
when currying so many functions, it is easier to think as the commented function as below:
(** The form **)
let rec mul ss ts =
    match (ss,ts) with
    | ([],_) -> []
    | (_,[]) -> []
    | (X::st,_) -> let NLST = mul st (mulX ts) 
                   add (mulC X ts) NLST;;
***)
let rec mul (ss : Poly) (ts : Poly) : Poly =
    match (ss,ts) with
    | ([],_) -> []
    | (_,[]) -> []
    | (X::st,_) -> add (mulC X ts) (mul st (mulX ts));;
mul [2;3;0;1] [1;2;3];;
mul [0;3;2] [0;3;2];;
mul [0; 0; 9; 12; 4] [0;3;2];;

(*** eval: int-> Poly -> int
If P(x) is a polynomial and a is ans integer, then the eval function should compute the 
integer value P(a). For instance, if P(x)=2+3x+x^3 then P(2)=2+3*2+2^3=16, this is int-
erpreted by 
    eval 2 [2;3;0;1] = 16

(** Other form **)
let rec eval s ts = 
    match ts with
    | [] -> 0
    | X::tt -> let NC = eval s (mulC s tt)
               X + NC;;
***)
let rec eval s (ts : Poly) =
    match ts with
    | [] -> 0
    | X::tt -> X + eval s (mulC s tt);;

eval 2 [2;3;0;1]

(*** Other method 
Higher-order function
1. apply power function to the integer substitution for each order.
2. a helper function to add the value of each term
***)
let rec powerI b e =
    match e with
    | 0 -> 1
    | N when N>0 -> b * powerI b (N-1)
    | _ -> failwith "negative exponent is not allowed for the function."
powerI 2 3;;
let rec eval1H f s ts e =
    match ts with
    | [] -> 0
    | X::tt -> X * f s e + eval1H f s tt (e+1);;
eval1H powerI 2 [2;1] 3;;
let evalT s ts = eval1H powerI s ts 0;;

evalT 2 [2;3;0;1];;



