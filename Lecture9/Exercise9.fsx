(* tail-recursive / iterative sum 
    where sum(m,n)=m + (m+1) + ... + (m+(n-1)) + (m+n)
    for m>=0 and n>=0
*)
let rec sum(m,n) =
    match (m,n) with
    | (_,0) -> m
    | (_,_) -> sum(m+n,n-1)
let fSum(m,n) = if m<0 || n<0 
                then failwith "m and n should be greater or equal than 0."
                else sum(m,n)

(* declare iterative function which does List.length *)
let rec fListLength n =
    function
    | [] -> n
    | _::xt -> fListLength (n+1) xt;;


(* consider following functions *)
let rec f n = 
    function 
    | 0 -> 1
    | k when k>0 -> n * (f n (k-1))
    | _ -> failwith "illegal argument";;
let rec g p f = 
    function
    | [] -> []
    | x::xs when p x -> f x :: g p f xs
    | _::xs -> g p f xs;;
type T = | A of int
         | B of string
         | C of T*T;;
let rec h = 
    function
    | A n -> string n
    | B s -> s
    | C(t1,t2) -> h t1 + h t2;;
(* Example of function applications, f, g and h. *)
(* f is a power function only takes positive exponents *)
f 2 3;;

(* g is a function maps a list A to a list B which elements of A satisfies predicate p *)
let pEven n = n%2=0;;
let fInc n = n+1;;
g pEven fInc [0;1;2;3;4;5;6;7;8];;

(* h is a function which convert type T variable to string *)
h (C(A 1,B "1"));;

(* Analysis of f, g and h regarding to 
    most general type 
    what the functions compute    
*)

(* f 
    1. The arguments are n and an anonymous argument arg1. 
    So we can lable them with fresh general type as beglow:
        n: T1   arg1: T2

    2. The pattern expression are integers, the wild card represents
    the pattern is less than 0, we can label them as below:
        k: T3

    3. The value expressions are integers 1, n * (f n (k-1)) and failwith 
    "illegal argument". The built-in function has type string->'a. 
    This means in F# the value of failwith "illegal argument" has 
    most general type. We can label the other expressions as below:
        1: int  n * (f n (k-1)): int

    4. Now we can unify the types such as 
        T1 = T2 = T3 int

    5. Since there are no futher constraints, in F# we have
        f: int -> int -> int

    The function computes power of n
    f n k = n^k    

    g
    1. The arguments are p, f and an anonymous argument arg1.
    We can label them with fresh general type.
        p : T1   f : T2   arg1 : T3
    
    2. The pattern expressions are lists, we lable them as:
        [] : T4 list    x::xs : T4 list     x : T4  p:T4 -> bool

    3. The value expressions are lists and we lable them as:
        [] : T5 list    f x :: g p f xs : T5 list   g p f xs : T5 list  f: T4 -> T5

    4. Now we can unify the types as: 
        T1=T4 -> bool
        T2=T4 -> T5 
        T3=T4 list
    
    5. In F#, we have the most general type such as:
        g: p:'a -> bool -> f:'a -> 'b list -> 'a list -> 'b list

    The function maps elements of list A to elements of list B which elements of A satisfies a predicate p
    
    h
    1. The argumment is an anonymous argment arg1.
    We can label it as below:
        arg1 : T1

    2. The pattern expressions are constructed with type T 
    constructors. So we can label them as below:
        A n : T     B s : T     C(t1,t2) : T

    3. The value expressions are strings. string: 'a -> string.
    So we can label them as below
        string n : string   s : string      h t1 + h t2 : string    n : int

    4. We can unify the types as 
        T1 = T
    
    5. There are no further constraints, in F# the types are 
    renamed with the most general type such as 
        h : T -> string

    The function converts type T variables to string.
*)

(* Tail-recursive variant of function f *)
let rec fA n =
    function 
    | 0 -> n
    | k when k>0 -> fA (n*k) (k-1)
    | _ -> failwith "It an't work for negative exponents.";;

(* Consider the following functions g1 and g2 *)
let rec g1 p = 
    function
    | x::xs when p x -> x::g1 p xs
    | _ -> [];;

let rec g2 f h n x =
    match n with
    | _ when n<0 -> failwith "negative n is not allowed"
    | 0 -> x
    | n -> g2 h f (n-1) (f x);;

(* Analysis of g1 and g2 regarding to 
    most general type 
    what does the function compute
*)
(*
    g1:
     1. The arguments of the function are p and an anonymous 
     argument arg1. We can label them with fresh types as:
        p : T1   arg1 : T2

     2. The pattern expressions are list and a wild card which 
     matches empty list. We can label them as:
        x::xs : T3 list     [] : T3 list    x: T3   p: T3 -> bool

     3. The value expressions can be labeled as below:
        x:: g1 p xs : T4 list   [] : T4 list 

     4. Now we can unify the types as below:
        T2 = T3 list = T4 list 

     5. There are no further constraints and in F# g has the most 
     general type such as:
        g: p:'a -> bool -> 'a list -> 'a list

    g2:
     1. The arguments of the function are f h n x. We can label 
     them as:
        f : T1  h : T2  n : T3  x : T4 
     
     2. The pattern expressions are integer and the wild card pattern
     matches to any integer value. We can label them as below:
        n : int 

     3. The value expression has a built-in function where 
     failwith: string -> 'a. We can label other expressions as:
        x : T4  g2 h f (n-1) (f x) : T4     f: T4 -> T4     

     4. Now we can unify the types as:
        T1 = T2 = 'a -> 'a
        T3 = int 
        T4 = 'a

     5. There are no further constraints, in F# we have
        g2: f:'a -> 'a h: 'a -> 'a -> n: int -> x:'a 
        
     What the functions compute?

     If the first element x of xs satisfies p x then g1 p xs 
     computes a list xs' has the same type with xs where the 
     elements xs' are the elements of xs satisfies predicaate p
     else, the list is empty.

     g2 f h n x computes 

     n=0 ->                         x0 = f0(x1) = f0(h1(f1(x3))) 
     n=1 ->                         x1 = h1(x2) = h1(f1(x3))
     n=2 ->                         x2 = f1(x3)
     n=3 ->                         x3 
     ...
     n-1 ->                         xn-1 
     n   ->                         xn  
     if n is an odd number then xn-1 = hn-2(xn)
     if n is an even number then xn-1 = fn-2(xn)
*)

(* Improve the function g1 to be a tail-recursive one *)
(* Tail recursive function with accumulating parameter. *)
let rec g1A acc p =
    function
    | x::xs when p x -> g1A (x::acc) p xs
    | _ -> List.rev acc;;
(* with continuation-based tail-recursive *)
let rec g1C c p =
    function 
    | x::xs when p x -> g1C (fun xt -> c (x::xt)) p xs
    | _ -> c [];;
g1 (fun x-> x<4) [1;2;3];;
g1C id (fun x-> x<4) [1;2;3];;
g1A [] (fun x-> x<4) [1;2;3];;

(*3. Explain why g2 is tail recursive. 
Because of each evaluation of n is bind to the function, thus no pending operations and size of stack frame is not grown.
The parameters are binded in the heap. (For list, only the size of heap is grown as the growm of linked list.)
Space demand is constant and time complexity is propositional to n.
*)

(* Consider following functions
*)
let rec f9 x =
    function
    | []    -> []
    | y::ys -> (x,y)::f9 x ys;;

let rec allPairs xs ys =
    match xs with
    | [] -> []
    | x::xrest -> f9 x ys @ allPairs xrest ys;;

(* Analysis of the functions f9 and allPairs *)
(*
    f9
     1. The arguments of the function can be labeled with 
     fresh types such as below:
        x : T1  arg1 : T2 
     
     2. The pattern expresssions of the function can be 
     labeled as:
        [] : T3 list    y::ys : T3 list     y : T3

     3. The value expressions can be labeled as:
        [] : T4 list    (x,y)::f9 x ys : T4 list

     4. We can unify the types as below:
        T2 = T3 list
        T4 list = (T1 * T3) list

     5. In F# we have 
        T1='a 
        T2= T3 list = 'b list
        T4 list = ('a * 'b) list
        f9: x:'a -> 'b list -> ('a * b) list

    allPairs
     1. The argument of the functions can be labeled as:
        xs : T1     ys : T2

     2. The pattern expressions can be labeled as:
        [] : T3 list    x::xrest : T3 list  x: T3   xrest: T3 list 

     3. @ has type 'a list -> 'a list -> 'a list. And the value 
        expression can be labeled as:
        [] : T4 list    f x ys @ allPairs xrest ys : T4 list
        f9 x ys : T3 -> T2 -> T4 list 

     4. We can unify the types as:
        T1= T3 list

     5. In F# we can rename the type of the function as:
        T1 = T3 list = 'a list
        since we have  f9: x:'a -> 'b list -> ('a * 'b) list
        T2 = 'b list 
        T4 list = ('a * 'b) list
        so
        allPairs: 'a list -> 'b list -> ('a * 'b) list 
*)
f9 "a" [1;2;3];;

(* Give an evaluation of the example above *)
(*  f9 "a" [1;2;3]
~>  ("a",1)::([2;3])
~>  ("a",1)::(("a",2)::[3])
~>  ("a",1)::(("a",2)::(("a",3)::[]))
~>  ("a",1)::(("a",2)::[("a",3)])
~>  ("a",1)::[("a",2);("a",3)]
~>  [("a",1);("a",2);("a",3)]
*)

(* Type analysis of 
    f "a" [1;2;3]
*)
(* Since function f has most general type as
    f: 'a -> 'b list -> ('a * 'b) list
    "a" : string
    [1;2;3] : int list
   so 
    'a is substitute with string and 'b list is substitute 
    with int list.
*)

(* Why f9 is not tail recursive? *)
(* Because :: cons operater make the link between head of 
list and the tail of the list. When the last function is 
called there are still pending operation which is the cons
left.
*)

(* Give a tail-recursive version of f9 based on an 
accumulating parameter. *)
let rec f9A acc x =
    function
    | [] -> List.rev acc
    | y::ys -> f9A ((x,y)::acc) x ys;;
(* Declare another version of f9 with higher-order function
from the List library *)
let f9L x ys = List.foldBack (fun y acc -> (x,y)::acc) ys [];;




