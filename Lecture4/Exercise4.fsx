(*Exercise 4*)
(** Exercise from Lecture 4 **)
(*** Declare a function g such as follows:
    g [x_1,...x_n] = [(x_1)^2+1,...,(x_n)^2]
***)
#load "..\Polynomials\Part1.fsx"
open Part1
let g xs = 
    List.map (fun X -> 
        powerI X 2 + 1) xs;;
g [2;3;4];;

(*** Declare a function such as follows: 
        disjoint xs ys 
     which is true when there are no common elements in the lists xs and ys, and false otherwise. 
***)
let disjoint xs ys = 
    List.forall (fun X -> 
            List.forall (fun Y -> X<>Y) ys) xs;;

disjoint [] [5;6;7;8];;

(*** Declare a function 
        subset xs ys
     which is true when every element in the lists xs is in ys, and false otherwise.
***)
let subset xs ys = List.forall (fun X -> 
                        List.exists (fun Y -> X=Y) ys) xs;;
subset [] [1;2;3;4];;

(*** Declare a function 
        inter xs ys
     which contains the common elements of the list xs and ys i.e. their intersection.
***)
let inter xs ys = 
    List.filter (fun X -> 
            List.exists (fun Y -> X=Y) ys) xs;;
inter [1;2;3] [1;2;3;4];;

(***
     An insertion function is declared as follows:

     Declare a union function on sets, where a set is represented by a list 
     without duplicated elements.
***)
let insert x ys = 
    if List.contains x ys then ys 
    else x::ys;;
let union xs ys = 
    List.foldBack (fun X _ -> 
            insert X ys) xs [];;
union [1;2;3] [4;2;3;1;];;

(** HR 5.3 
Solve exercise 4.12 with List.fold or List.foldBack.
HR 4.12 
    Declare a function sum(p,xs) to sum up the elements in xs that satisfying the predicate p.
    Test the function on different predicates (e.g., p(x) = x > 0)
**)
#load "..\Lecture2\Exercise2.fsx"
#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"
open FsCheck

Exercise2.sum(Exercise2.p4_12,[1;2;3;4]);;
(* Comment: Uppercase identifier shouldn't generally be used. As the F# compiler have given a warning in the following ... "fun ACC " ...*)
let fSumF(p,xs) = 
    List.fold (fun acc X -> 
        if p(X) then X+acc
        else acc) 0 xs;;
fSumF(Exercise2.p4_12,[1;2;3;4])
let fSumFB(p,xs) = 
    List.foldBack (fun acc X -> 
        if p(X) then X+acc
        else acc) xs 0;;
let ppfSumFVsum xs = 
    fSumF(Exercise2.p4_12,xs)=Exercise2.sum(Exercise2.p4_12,xs);;
let _ = Check.Quick ppfSumFVsum;;
let ppfSumFBVsum xs = 
    fSumF(Exercise2.p4_12,xs)=Exercise2.sum(Exercise2.p4_12,xs);;
let _ = Check.Quick ppfSumFBVsum;;

(** Revised version of the Cash Register example in Section 4.6.
    1. Use List.tryFind to replace the function findArticle.
    2. Use List.foldBack to replace the function makeBill.
**)
(*** HR page 98, function  findArticle: string -> (string*'a) list -> 'a ***)
let rec findArticle ac = function 
    | (ac',adesc)::_ when ac=ac' -> adesc
    | _::reg -> findArticle ac reg
    | _ -> failwith(ac + " is unknown article code.");; 

let fFindArticleTF ac reg = 
    match List.tryFind (fun (X,_) -> ac=X) reg with 
    | Some (_,Y) -> Y
    | None -> failwith(ac + " is unknown article code.");;

let ppfFindArticleTFVfindArticle (ac:string) (reg:(string*(string*int)) list) = 
    fFindArticleTF ac reg = findArticle ac reg
let _ = Check.Quick ppfFindArticleTFVfindArticle;;
(* Comment: Given exceptions by using "failwith" makes the property falsifiable when non-exsiting values. In this case, unit testing makes more sense. *)
let reg1 = [("a1",("cheese",25));
           ("a2",("herring",4));
           ("a3",("soft drink",5))];;
findArticle "a1" reg1 = fFindArticleTF "a1" reg1;;


(*** HR page 98, function makeBill: (string * ('a * int)) list -> (int * string) list -> (int*'a*int) list * int ***)
let rec makeBill reg = function
    | [] -> ([],0)
    | (np,ac)::pur -> let (aname,aprice) = findArticle ac reg
                      let tprice = np*aprice
                      let (billtl,sumtl) = makeBill reg pur
                      ((np,aname,tprice)::billtl,tprice+sumtl);;

let fMakeBillFB reg purs = 
    List.foldBack (fun (np,ac) (detail,gross) -> 
            let (N,P) = fFindArticleTF ac reg
            let sum = np*P
            ((np,N,sum)::detail,gross+sum)) purs ([],0)

(*** unit test***)
let pur1 = [(3,"a2"); (1,"a1")];;
makeBill reg1 pur1 = fMakeBillFB reg1 pur1;;

(*** List.fold version of makeBill function. Order would be reversed. ***)
let fMakeBillF reg purs = 
    List.fold (fun (detail,gross) (np,ac) -> 
            let (N,P) = fFindArticleTF ac reg
            let sum = np*P
            ((np,N,sum)::detail,gross+sum)) ([],0) purs

(** Solve the problems in old exams by first using "plain" recusive functions. Then using function from the List library. 
    1. Problem 2 from Exam, summer 2015
    2. Problem 1 qeustions 1-5 from Exam, Fall 2013.
**)

(*** Problem 2 ***)
(**** 1. Declare a function mixMap so that
        mixMap f [x_0;...x_m] [y_0;...;y_m]
      = [f(x_0,y_0);...f(x_m,y_m)]
****)
let rec mixMap f xs ys =
    match (xs,ys) with
    | (X::xt,Y::yt) -> f (X,Y)::mixMap f xt yt
    | ([],[]) -> []
    | _ -> failwith "Two list have different length.";;

let rec fMix xs ys =
    match (xs,ys) with
    | (X::xt,Y::yt) -> (X,Y)::fMix xt yt
    | ([],[]) -> []
    | _ -> failwith "Two list have different length.";;
let fMixMapM f xs ys = 
    List.map (fun (X,Y) -> f(X,Y)) (fMix xs ys) ;;
let fMixMapFB2 f xs ys = 
    List.foldBack2 (fun X Y acc -> 
            f (X,Y)::acc) xs ys []

(***** Other method *****)
let rec fMix2List f xs ys =
    match (xs,ys) with
    | (X::xt,Y::yt) -> let zs = fMix2List f xt yt
                       f (X,Y)::zs
    | ([],[]) -> []
    | _ -> failwith "Two list have different length.";;

let rec fFn2List f xs ys = 
    match (xs,ys) with
    | ([],[]) -> []
    | (X::xt,Y::yt) -> f (X,Y) (fFn2List f xt yt)
    | _ -> failwith "Two list have different length.";;
let fMixMapAB f xs ys = fFn2List f xs ys

let fConEle (X,Y) zs = (X,Y)::zs
let rec fPair2List xs ys = 
    match (xs,ys) with
    | ([],[]) -> []
    | (X::xt,Y::yt) -> fConEle (X,Y) (fPair2List xt yt)
    | _ -> failwith "Two list have different length.";;

let f2015p2 (X,Y) = X+Y 
mixMap f2015p2 [1;3;5] [0;2;4];;
fMixMapM f2015p2 [1;3;5] [0;2;4];;
fMixMapFB2 f2015p2 [1;3;5] [0;2;4];;

(**** 2. Declare a function unmixMap so that
        unmixMap f g [(x_0,y_0);...;(x_n,y_n)] 
        = ([f x_0;...;f x_n],[g y_0;...;g y_n])
****)
let rec unmixMap f g zs = 
    match zs with
    | (X,Y)::zt -> let (xs,ys) = unmixMap f g zt
                   (f(X)::xs, g(Y)::ys)
    | [] -> ([],[])
let fUnmixMapFB f g zs =
    List.foldBack (fun (X,Y) (xs,ys) -> 
            (f(X)::xs), g(Y)::ys) zs ([],[])

(**** 3. Give the most general type of mixMap and unmixMap
        mixMap: ('a*'b->'c) -> 'a list -> 'blist -> 'c list
        unmixMap: ('a->'b) -> ('c->'d) -> ('a*'c) list -> 'b list * 'd list  
****)

(*** Problem 1, multiset
    Finite multiset is ms is represented as a list of pairs [(e_1,n_1);...(e_k,n_k)] 
        where an element (e_i,n_i) represents that e_i is a term and n_i is the number of occurences of the term.       
    A multiset representation must satisfy the multiset invariant,
        where every term is unique/distinct, i.e. e_i not equal to e_j for i not equal to j.
    Empty multiset is represented as empty list.
***)

(**** Type of the multiset is given as follows: ****)
type Multiset<'a when 'a : equality> = ('a * int) list;;

(**** 1. Declare a function inv: Multiset<'a> -> bool 
        where inv(ms) is true when ms satisfies the multiset invariant.
****)
let rec pNEfst y =
    function
    | [] -> true
    | (X,_)::xs ->  X<>y && pNEfst y xs;;

let rec inv ms =
    match ms with
    | [] -> true
    | (M,V)::mt -> pNEfst M mt && V>0 && inv mt;;

let rec pInvMs = 
    function
    | [] -> true
    | (M,N)::mt -> List.forall (fun (K,V) -> 
                        K<>M) mt && N>0 && pInvMs mt;;


(**** 2. Declare a function insert: 'a -> int -> Multiset<'a> -> Multiset<'a>, 
            where insert e n ms increases the occurencies of a term 'e' by 'n'. 
****)
let rec insertF13 e n ms =
    match ms with
    | [] -> []
    | (X,c)::mt -> if X=e then (X,c+n)::insertF13 e n mt
                   else (X,c)::insertF13 e n mt;;
let fInsertF13FB e n ms =
    List.foldBack (fun (X,c) nms -> 
        if X=e then (X,c+n)::nms
        else (X,c)::nms) ms [];;

(**** 3. Declare a function numberOf e ms 
            projects the second term of a pair in 'ms' if the first term is equal to 'e'.
         State the type of the function.
****)
let rec numberOf e ms =
    match ms with
    | (X,c)::mt -> if X=e then c
                   else numberOf e mt
    | [] -> 0;;
(***** numbserOf: 'a -> ('a*int) list -> int when 'a : equality *****)

let fNumberOfF e (ms: ('a*int) list) = 
    match List.tryFind (fun (X,_) -> 
        X=e) ms with
    | Some (_,c) -> c
    | None -> failwith "The element is not exist in the multiset.";;

(**** 4. Declare a function delete, minus 1 to second term of every pair in the list 
            if the first term of the pair is equal to e.
****)
let rec delete e ms =
    match ms with
    | (X,c)::mt -> if X=e then (X,c-1)::mt
                   else (X,c)::delete e mt
    | [] -> [];;
let fdeleteFB e ms =
    List.foldBack (fun (X,c) acc ->
        if X=e then (X,c-1)::acc
        else (X,c)::acc) ms []

(**** 5. Declare a function union: Multiset<'a> * Multiset<'a> -> Multiset<'a> 
            for the first terms of the pairs if they are unique to the other multiset, then the pair remain the same.
                else sum up the two second terms for the same first terms.
****)
let rec unionF13 ys xs  =
    match xs with
    | (X,c)::xt -> if pNEfst X ys then (X,c)::unionF13 ys xt
                   else unionF13 (insertF13 X c ys) xt
    | [] -> ys;;
let cUnionXs = [('a',1);('b',2);('c',3)];;
let cUnionYs = [('a',3);('b',4);('d',7)];;
unionF13 cUnionXs cUnionYs;;

let rec fUnionFB ys xs = 
    List.foldBack (fun (X,c) acc ->
        if pNEfst X ys then (X,c)::acc
        else insertF13 X c acc) xs ys;;
fUnionFB cUnionXs cUnionYs;;
