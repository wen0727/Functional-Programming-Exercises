(* Exercise 2 *)
(** Let-expressions **)
let gL y = let a = 6
           let b = y + a
           y + b
gL 1

(*** 
The meaning of the function:
    let g y = exp1 
is equivalent to 
    let g = fun y->exp1
    exp1:
        let a = 6 
        let b = y + a 
        y+b
    is equivalent to 
        let a = 6 in let b = y+a in y+b
        where 
the binding in the expresison y+b
    y+b[b->y+a,a->6]
is equivalent to
    2y+6
let g = fun y -> 2y+6
***)

(*** sumProd: int list -> int*int:
Declare a function where the result is the pair consits sum and product of the elements.
***)
let rec sumProd =
    function
    | [] -> (0,1)
    | e::et -> let (sum,prod) = sumProd et
               (e+sum,e*prod)
sumProd [2;5]

(** Blackboard exercise 
A function from the List library:
    List.unzip([(x_0,y_0);(x_1,y_);...;(x_n-1,y_n-1)]) 
        = ([x_0;x_1;...;x_n-1],[y_0;y_1;...;y_n-1])
**)
let rec unzip = 
    function
    | [] -> ([],[])
    | (x,y)::zt -> let (xs,ys) = unzip zt
                   (x::xs,y::ys)
unzip ([(0,1);(0,1);(0,1)])
(** 1. **)
(*** HR 2.1
Declare a function f: int ->bool such that f(n)=true exactly whene n is divisible by 2 
or divisible by 3 but not divisible by 5. Write down the expected values of f(24), f(27), f(29) 
and f(30) and compare with the result. Hint: n is divisble by q when n%q=0. 
***)
let f2_1 n = n%2=0 || n%3=0 && n%5<>0
f2_1 7
(*** HR 2.2
Declare a function pow: string*int -> string, where
    pow(s,n)=s (central dot) s (central dot) ...(central dot) s for n times
where we use (central dot) to denote string concaternation. (The F# representation is +.)
***)
let rec pow (s,n) =
    match n with
    | 0 -> ""
    | n when n>0 -> s+pow (s,n-1)
    | _ -> failwith "n must be positive integer";;
pow ("s",3);;

(*** HR 2.13
The functions curry and uncurry of types 
    curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
    uncyrry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c 
are define in the following ways:
    curry f is the function g where g x is the function h where h y= f(x,y).
    uncurry g is the function f where f(x,y) is the value h y for the function h = g x.
Write declarations of curry and uncurry.

Definition of currying:
    given function :
        f: (A x B) -> C
    currying :
        h: A -> (B -> C)

Definiction of uncurrying:
    given function :
        f: A -> (B -> C)
    uncurrying :
        h: (A x B) -> C
***)

let curry f g h = f(g,h)
let uncurry f (g,h) = f g h

(*** HR 4.3 
Declare function evenN: int -> int list such that evenN n generates the list of the first 
non-negative even numbers.
***)

let rec evenN n =
    match n with 
    | n when n>=0 -> if n%2=0 then n::evenN (n-2)
                     else evenN (n-1)
    | _ -> [];;

evenN 10;;


let rec evenN1H X N =
    match N with 
    | n when n<=X -> let EVENS = evenN1H X (n+2)
                     n::EVENS
    | _ -> [];;
let evenN1 X = if X%2=0 then evenN1H X 0
               else evenN1H (X-1) 0;;
evenN1 10

(*** HR 4.8 
Declare an F# function split such that:
    split [x_0;x_1;x_2;x_3;...;x_n-1]=([x_0;x_2;...],[x_1;x_3;...])
***)
let rec split = function
    | [] -> ([],[])
    | [x] -> ([x],[])
    | x0::x1::xt -> let (AN,BN) = split xt
                    (x0::AN,x1::BN);;
split [0;1;2;3;4;5];;

(*** HR 4.9
Declare an F# function zip such that:
    zip ([x_0;x_1;...;x_n-1;],[y_0;y_1;...;y_n-1])
    =[(x_0,y_0);(x_1,y_1);...;(x_n-1,y_n-1);]
***)
let rec zip = function
    | (_,[]) -> []
    | ([],_) -> []
    | (x::xt,y::yt) -> let ZS = zip(xt,yt)
                       (x,y)::ZS;;
zip([0;2;4],[1;3;5]);;

(*** HR 4.12
Declare a function sum(p,xs) where p is a predicate of type int -> bool and xs is a list of 
integers. The value of sum(p,xs) is the sum of the elements in xs satisfying the predicate p. 
Test the function on different predicates (e.g,p(x)=x>0).
***)
let p4_12(x) = x>0
(*** Better method ***)
let rec sum(p,xs) =
    match xs with
    | [] -> 0
    | x::xt -> let SUM = sum(p,xt) 
               if p(x) then x+SUM
               else SUM;;
sum(p4_12,[0;1;2;3]);;

(*** HR 4.16
consider the declarations:
    let rec f = function
        | (x,[]) -> []
        | (x,y::ys) -> (x+y)::f(x-1,ys);;

    let rec g = function
        | [] -> []
        | (x,y)::s -> (x,y)::(y,x)::g s;;

    let rec h = function
        | [] -> []
        | x::xs -> x::(h xs) @ [x];;
(* Question *)
    Find the types for f, g and h and explain the value of the expressions:

(* Solution *)
    1. f(x, [y_0,y_1,...,y_n-1]), n>=0
        f: int*int list -> int list
        Because the type of x-1 is integer so 
            x : int
        Therefore the type of x+y is integer and 
            y : int
        The pattern is of the form (x,[]) so
            (x,[]) : int*int list
        We can derive the type of the function as
            f:int*int list -> int list

    2. g[(x_0,y_0),(x_1,y_1),...,(x_n-1,y_n-1)], n>=0
        g: 'a*'a list -> 'a*'a list
        Because the pattern is of the form (x,y)::s, we can assume
            (x,y)::s is type of 'a*'b list where x : 'a and y : 'b
        Then we have the binding (x,y)::(y,x)::g s.
        Since the order of the pair is changed and the element of the list must have the same typle therefore we can derive that 
            x : 'a and y : 'a
        Thus, We can derive
            g: ('a*'a) list -> ('a*'a) list
    3. h[x_0,x_1,...,x_n-1], n>=0
        h: -> 'a list -> 'a list
        Becase the pattern is of the form x::xs, we can assume 
            x::xs : 'a list where x : 'a
        The binding has the form  x::(h xs) @ [x], where x::(h xs) is 'a list, [x] is 'a list and @ is library list appending function.
        Thus, we can derive
            h: -> 'a list -> 'a list
***)

(** 2. 
Consider the solution to 4.7 and make an evaluation of multiplicity 2 [1;2;8;2] 

The solution: 
    let rec multiplicity x xs =
        match xs with
        | [] -> 0
        | e::xt when e=x -> 1 + multiplicity x xt
        | _::xt -> multiplicity x xt;;

Evaluation:
    multiplicity 2 [1;2;8;2]
~>   (multiplicity x xt,[x->2, e->1, xt->[2;8;2])
~>   (1+multiplicity x xt,[x->2, e->2, xt->[8;2])
~>   (1+multiplicity x xt,[x->2, e->8, xt->[2])
~>   (1+1+multiplicity x xt,[x->2, e->2, xt->[])
~>   1+1+0
~>   2
**)

(** 3. 
Addendum to exercise on polynomials part 1, declare a higher-order function: f so that 
add = f(+) and sub = f(-)
**)
#load "..\Polynomials\Part1.fsx";;
open Part1
let (+) P Q = add P Q;;
(+) [1;2;3] [1;2;3];;
let (-) P Q = sub P Q;;
(-) [1;2;3] [1;2;3];;



