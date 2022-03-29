#time
(* Exercise week 12 *)
(** oldExamWeek13 **)
(*** Problem 1 ***)
type Title = string;;
type Section = Title * Elem list
and Elem = Par of string | Sub of Section;;
type Chapter = Title * Section list;;
type Book = Chapter list;;
let sec11 = ("Background", [Par "bla"; Sub(("Why programming", [Par "Bla."]))]);;
let sec12 = ("An example", [Par "bla"; Sub(("Special features", [Par "Bla."]))]);;
let sec21 = ("Fundamental concepts",[Par "bla"; Sub(("Mathematical background", [Par "Bla."]))]);;
let sec22 = ("Operational semantics", [Sub(("Basics", [Par "Bla."])); Sub(("Applications", [Par "Bla."]))]);;
let sec23 = ("Further reading", [Par "bla"]);;
let sec31 = ("Overview", [Par "bla"]);;
let sec32 = ("A simple example", [Par "bla"]);;
let sec33 = ("An advanced example", [Par "bla"]);;
let sec41 = ("Status", [Par "bla"]);;
let sec42 = ("What’s next?", [Par "bla"]);;
let ch1 = ("Introduction", [sec11;sec12]);;
let ch2 = ("Basic Issues", [sec21;sec22;sec23]);;
let ch3 = ("Advanced Issues", [sec31;sec32;sec33]);;
//let ch3 = ("Advanced Issues", [sec31;sec32;sec33;sec34]);;
let ch4 = ("Conclusion", [sec41;sec42]);;
let book1 = [ch1; ch2; ch3; ch4];;

(**** Q1 ****)
let rec maxL = 
    function
    | [] -> 0
    | [x] -> x
    | x::y::xs -> maxL((max x y)::xs);;
//max impelementation
let comp x y =
    if x>y then x
    else y;;

let overview xs = List.map (fun (t,_) -> t) xs;;
//List.map implementation
let rec fMap f = 
    function
    | [] -> []
    | x::xt -> f x :: fMap f xt

(**** Q2 ****)
let rec depthSection (_,es) = 
    1 + maxL(List.map depthElem es)
and depthElem =
    function
    | Par _ -> 0
    | Sub s -> depthSection s;;

let depthChapter (_,ss) = 
    1 + maxL(List.map (fun x -> depthSection x) ss);;

let depthBook cs = 
    maxL(List.map (fun x -> depthChapter x) cs);;


(**** Q3 ****)

let rec tocB cs = 
    fTocChp 1 cs 
and fTocChp ce =
    function
    | [] -> []
    | (t,ss)::ct -> ([ce],t)::fTocSecs [ce] 1 ss @  fTocChp (ce+1) ct
and fTocSecs ns se = 
    function
    | [] -> []
    | s::st -> fTocSec ns se s @ fTocSecs ns (se+1) st
and fTocSec ns se (t,es) =
    let nNs = ns@[se] 
    (nNs,t)::fTocElems ns 1 es
and fTocElems ns ee = 
    function
    | [] -> []
    | Par _ :: et -> fTocElems ns ee et
    | Sub s :: et -> fTocSec ns ee s @ fTocElems ns (ee+1) et;;
tocB book1

(*** Problem 2 ***)
let rec f xs ys = 
    match (xs,ys) with
    | (x::xs1, y::ys1) -> x::y::f xs1 ys1
    | _ -> [];;
(**** Q1 Evalueation 
            f [1;6;0;8] [0;7;3;3]
        ~>  1::0::f [6;0;8;] [7;3;3]
        ~>  1::0::6::7::(f [0;8] [3;3]
        ~>  1::0::6::7::0::3::f [8] [3]
        ~>  1::0::6::7::0::3::8::3::f [] []
        ~>  1::0::6::7::0::3::8::3::[]
        =   [1;0;6;7;0;3;8;3]
****)

(**** Q2 Give type for function f and describe what f computes.
    Type analysis
    (1. The arguments of function f are xs and ys, so we can lable them with fresh general types as below
            f : T1       xs : T2     ys : T3
    
    2. The pattern expresison is a pair, we can lable the pattern with fresh types
            (x::xs1, y::ys1) : T4 list * T5 list    where x : T4      y : T5
       The wild card pattern represents ([],[]).
    
    3. The value expression is list, we can lable them with fresh type
            x::y::f xs1 ys1 : T6 list       [] : T6 list    where x : T6      y : T6        f xs1 ys1 : T6 list 
    
    4. Now we can unify the types such as
            T1=T2=T3=T4=T5=T6

    5. Since there are no further constraints, so in F# we have)
            f : 'a list -> 'a list -> 'a list
    1. The most genneral type:
        f : 'a list -> 'a list -> 'a list
    2. It computes
        f [x1;...xi] [y1;...yj] = [x1;y1;...xn;yn] where n is minimun between i and j.
****)
(**** Q3 Explain why function f is not tail recursive and give a tail recursive version of the function f based on accumulating parameter
    Why?
        It is because the recursive call of the function is not a tail call. When f xs1 ys1 returns a value zs, the expression x::y::zs must be computed.
        Moreover, there is neither accumulating parameter nor continuation-based argument.
let rec fI xs ys acc  =
    match (xs,ys) with
    | (x::xt,y::yt) -> fI xt yt (acc @ [x;y])
    | _ -> acc
****)
let rec fI xs ys acc  =
    match (xs,ys) with
    | (x::xt,y::yt) -> fI xt yt (y::x::acc)
    | _ -> List.rev acc

f [1;2;3;4] [5;6;7;8]
fI [1;2;3;4] [5;6;7;8] []

(**** Q4 Declare a continuation-based tail-recursive version of function f.
****)
let rec fC xs ys c =
    match (xs,ys) with
    | (x::xt,y::yt) -> fC xt yt (fun tail -> c (x::y::tail))
    | _ -> c []
fC [1;2;3;4] [5;6;7;8] id

(*** Problem 3 ***)

let rec f = function
            | 0 -> [0]
            | i when i>0 -> i::g(i-1)
            | _ -> failwith "Negative argument"
and g = function
        | 0 -> []
        | n -> f(n-1);;
(**** Q1 
        1. Give the value of f 5 and h (seq [1;2;3;4] (fun i -> i+10))
        2. Give most general type of the two functions
           2.1 what do they compute.

****)
f 5
(**** 
    1. 
        f 5
    ~> 5::g 4
    ~> 5::f 3
    ~> 5::3::g 2
    ~> 5::3::f 1
    ~> 5::3::1::g 0
    ~> 5::3::1::[]
    =  [5;3;1]
    2. The type of function f:
            f: int -> int list
            and g: int -> int list
       2.1 If i is negative f i raises an exception,
           if i is positive and obb integer, then f i = [i; i-2; ...; 1]
           otherwise f i = [i; i-2; ...; 0]        
****)
// Recap of sequence library
fun () -> 2 + 5
//the value is held in the function
it();;
//7
let idWithPrint i = let _ = printfn "%d" i
                    i;;
idWithPrint 7;;


fun () -> (idWithPrint 7) + (idWithPrint 11);;
//the value is held in the function

let s123a = 
    seq {yield 1
         yield 2
         yield 3 };;
s123a

let ex1 = 
    seq {
        for x in 1..10 do
            yield x
            yield! seq { for i in 1..x -> i}
    }

let h s k = 
    seq {
        for a in s do   
            yield k a
    };;

h (seq [1;2;3;4]) (fun i -> i+10)

(**** 
    1. 
        h (seq [1;2;3;4]) (fun i -> i+10)
    =   seq [11; 12; 13; 14]
    2. The type of function h:
            h: seq<'a> -> ('a->'b) -> seq<'b>
       2.1 h s k computes a sequence by applying function k to every element in the sequence s.
****)
(*** Problem 4 ***)
(**** Q1 
type Container =
    | Tank of float * float * float // (length, width, height)
    | Ball of float // radius
Tank (1.0,1.0,1.0);;
Ball 1.0;;
****)
(**** Q2 isWF: Container -> bool , container is well formed if the parameters of attributes are all positive.
let isWF =
    function
    | Tank (l,w,h) -> l>0.0 && w>0.0 && h>0.0
    | Ball r -> r>0.0;;
****)
(**** Q3 volume: Container -> float
let volume = 
    function 
    | Tank (l,w,h) -> l*w*h
    | Ball r -> 4.0/3.0 * System.Math.PI * r * r * r;;
****)
(**** Q4 Extend Cylinder to the Container and modify the functions accrodingly. ****)
type Container =
    | Tank of float * float * float 
    | Ball of float 
    | Cylinder of float * float
let isWF1 =
    function
    | Tank (l,w,h) -> l>0.0 && w>0.0 && h>0.0
    | Ball r -> r>0.0
    | Cylinder (r,h) -> r>0.0 && h>0.0;;
let volume = 
    function 
    | Tank (l,w,h) -> l*w*h
    | Ball r -> 4.0/3.0 * System.Math.PI * r * r * r
    | Cylinder (r,h) -> System.Math.PI * r * r * h;;

type Name = string
type Contents = string
type Storage = Map<Name, Contents*Container>

(**** Q5 value of storage ****)
Map.ofList [("tank1",("oil",Tank (1.0,1.0,1.0)))];;
Map.ofList [("ball1",("water", Ball 1.0))];;

(**** Q6 find: Name -> Storage -> Contents * float ****)
let rec fFindP n stg =
    match stg with
    | [] -> failwith ("Warning: " + n + " doen't exist in the storage.")
    | (a,(b,c))::stgt -> if n=a 
                         then (b,volume c)
                         else fFindP n stgt;;
let findP n stg = fFindP n (Map.toList stg);;

let find n stg =
    match Map.tryFind n stg with
    | Some (b,c) -> (b,volume c)
    | None -> failwith ("Warning: " + n + " doesn't exist in the storage.");;

(*** Problem 4 May 2016 ***)
type T<'a> = L 
           | N of T<'a> * 'a * T<'a>;;
(**** Q1 Give the type of t and declare 3 values of type T<bool list> ****)
let t = N(N(L, 1, N(N(L, 2, L), 1, L)), 3, L);;
(***** T<int> *****)
let t1 = N(L,[true],L);;
let t2 = N(t1,[false],L);;
let t3 = N(t1,[false],t2);;

(**** Q2.1 ****)
let rec f g t1 t2 =
    match (t1,t2) with
    | (L,L) -> L
    | (N(ta1,va,ta2), N(tb1,vb,tb2)) -> N(f g ta1 tb1, g(va,vb), f g ta2 tb2);;

(**** f: ('a*'b ->'c) -> T<'c> 
    Type analysis:
    1. From the function declaration we can see, there are three arguments. 
       We lable them with most general types T1 and T2 type of tree and T3 type of tree.
       type of T3.
        g : T1      t1 : T<T2>     t2 : T<T3>
    
    2. The match expression constructs a pair of trees and labled as
        (L,L) : T<T2>*T<T3>     (N(ta1,va,ta2), N(tb1,vb,tb2)) : T<T2>*T<T3>
    
    3. The values are labled as below
        L : T<T4>      N(f g ta1 tb1, g(va,vb), f g ta2 tb2) : T<T4>
    
       In addition 
        g(va,vb) : T2*T3 -> T1      

    4. we can observe the unification of two types as T1=T4 and the type of the function is as following
        f: (T2*T3->T1)->T<T1>

    5. There are no further constraint, so we can rename the most general types as 
        f: g:('a*'b->'c)->T<'c>

    What does the function compute?
        The value of (f g t1 t2) is defined when t1 and t2 have the same structual.
        When the pattern is pair of leaves, the value is trivially a leaf.
        When the pattern is pair of nodes, the new node value is defined by applying function g to the node value of t1 and t2 at the same position.

   Graph:
        t1 :
            N
        ____|____
        |   x   |
        N       N
     ___|___ ___|___
     L  y  L L  z  L

     t2 :
            N
        ____|____
        |   o   |
        N       N
     ___|___ ___|___
     L  p  L L  q  L

    t :
            N
        ____|____
        |   v1  |
        N       N
     ___|___ ___|___
     L  v2 L L  v3 L

     where v1=g(x,o)    v2=g(y,p)   v3=g(z,q)
****)
let rec h t = 
    match t with
    | L -> L
    | N(t1, v, t2) -> N(h t2, v, h t1);;
(****
    h: T<'a> -> T<'a>
    The value of h t is the mirror image of t. The following graph shows an example of the funtion.

    Graph:
        t :
            N
        ____|____
        |   x   |
        N       N
     ___|___ ___|___
     L  y  L L  z  L

        t' :
            N
        ____|____
        |   v1   |
        N       N
     ___|___ ___|___
     L  v2  L L  v3  L

     where v1=x   v2=z  v3=y      
****)
let rec g = 
    function
    | (_,L) -> None
    | (p, N(t1,a,t2)) when p a -> Some(t1,t2)
    | (p, N(t1,a,t2)) -> match g(p,t1) with
                         | None -> g(p,t2)
                         | res -> res;;

(**** 
    g: ('a->bool)*T<'a> -> (T<'a>*T<'a>) option
    g (p,t) searchesfor a node which the value satisfies predicate p in depth-first left to right order.
    If such node exists then the value ise some (t1,t2)
    e.g 
    let p x = x>0
    
    Graph 
        t :
            N
        ____|____
        |   1   |
        N       N
     ___|___ ___|___
     L  2  L L  3  L

    g(p,t) = Some (N (L,2,L), N (L,3,L))
****)
(**** Q3 ****)
let rec count a t =
    match t with
    | L -> 0
    | N (t1,v,t2) -> let CL = count a t1
                     let CR = count a t2
                     if v=a
                     then 1 + CL + CR
                     else CL+ CR;;
count 1  t;;
(**** Q4 ****)
let rec replace a b t =
    match t with
    | L -> L
    | N (t1,v,t2) -> let RL = replace a b t1
                     let RR = replace a b t2
                     if v=a
                     then N (RL,b,RR)
                     else N (RL,v,RR);;
replace 1 0 t;;

