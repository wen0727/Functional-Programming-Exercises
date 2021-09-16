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
let rec add p q = 
    match (p,q) with
    | ([],_) -> q
    | (_,[]) -> p
    | (a::an,b::bm) -> (a+b)::add an bm;;

add [1;2] [3;4;5;6];;

(*** mulC: int -> Poly -> Poly *
The function mulC should implement the multiplication of a polynomial by a constant. For 
instance, 2(2+x^3)=4+2^3 and we represent this by
    mulC 2 [2;0;0;1] = [4;0;0;2]
**)
let rec mulC c p =
    match p with
    | [] -> []
    | a::an -> (c*a)::mulC c an;; 
mulC 2 [2;0;0;1];;

(*** sub: Poly -> Poly -> Poly 
Subtraction of two polynomials represented by lists is performed by element-wise substrac
-tions. For instance, (1+2x)-(3+4x+5x^2+6x^3)=-2-2x-5x6^2-6x^3 and we represent this as 
follows:
    sub [1;2] [3;4;5;6] = [-2;-2;-5;-6]
***)
let rec sub p q =
    match (p,q) with
    | ([],b::bm) -> -b::sub [] bm
    | (_,[]) -> p
    | (a::an,b::bm) -> a-b::sub an bm;;

sub [1;2] [3;4;5;6]
(*** mulX: Poly -> Poly
The multiplication function mulX should implement the multiplication of a polynomial by  
x. For instance, x(2+x^3)=2x+x^4 and we represent that by
    mulX [2;0;0;1]=[0;2;0;0;1]
***)
let mulX p =
    match p with
    | [] -> []
    | _ -> 0::p;;
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
let rec mul p q =
    match (p,q) with
    | ([],_) -> []
    | (_,[]) -> []
    | (a::an,_) -> let NLST = mul an (mulX q) 
                   add (mulC a q) NLST;;
***)
let rec mul p q =
    match (p,q) with
    | ([],_) -> []
    | (_,[]) -> []
    | (a::an,_) -> add (mulC a q) (mul an (mulX q));;
mul [2;3;0;1] [1;2;3];;

(*** eval: int-> Poly -> int
If P(x) is a polynomial and a is ans integer, then the eval function should compute the 
integer value P(a). For instance, if P(x)=2+3x+x^3 then P(2)=2+3*2+2^3=16, this is int-
erpreted by 
    eval 2 [2;3;0;1] = 16
***)
let rec eval s p =
    match p with
    | [] -> 0
    | a::an -> a + eval s (mulC s an);;

eval 2 [2;3;0;1]

(*** Other method 
Higher-order function
1. apply power function to the integer substitution for each order.
2. a helper function to add the value of each term
***)
let rec powerP x n =
    match n with
    | 0 -> 1
    | _ -> x * powerP x (n-1);;
powerP 2 3;;
let rec evalTe s p i =
    match p with
    | [] ->  0
    | a::an -> a * powerP s i + evalTe s an (i+1)
evalTe 2 [2;1] 3
let evalT s p = evalTe s p 0;;

evalT 2 [2;3;0;1];;

