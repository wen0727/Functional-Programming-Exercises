(* List 
type List<'a> = Head of 'a
              | Tail of List<'a>
*)
(** List.forall ('a->bool) -> 'a list -> bool **)
let rec pForAll p xs = 
    match xs with
    | [] -> true
    | x::xt -> p x && pForAll p xt;;

(** List.exists: ('a->bool) -> 'a list -> bool **)
let rec pExists p xs =
    match xs with
    | [] -> false
    | x::xt -> p x || pExists p xt;;

(** List.fold: ('a->'b->'a) -> 'a -> 'b list -> 'a **)
let rec fFold f acc xs =
    match xs with
    | [] -> acc
    | x::xt -> fFold f (f acc x) xt;;

(** List.foldBack: ('a->'b->'b) -> 'a list -> 'b -> 'b **)
let rec fFoldB f xs acc =
    match xs with
    | [] -> acc
    | x::xt -> f x (fFoldB f xt acc);;

(** List.tryFind: ('a->bool) -> 'a list -> 'a option **)
let rec fTryF p xs =
    match xs with
    | [] -> None
    | x::xt -> if p x
               then Some x
               else fTryF p xt;;

(** List.filter ('a->bool) -> 'a list -> 'a list **)
let rec fFilter p xs =
    match xs with
    | [] -> []
    | x::xt -> if p x 
               then x::fFilter p xt
               else fFilter p xt;;
(** List.map: ('a->'b) -> 'a list -> 'b list **)
let rec fMap f =
    function 
    | [] -> []
    | x::xt -> f x :: fMap f xt;;
(** List.collect: ('a -> 'b list) -> 'a list -> 'b list **)
//append: 'a list -> 'a list -> 'a list 
let rec (@) xs ys = 
    match xs with
    | [] -> []
    | x::xt -> x::(xt @ ys);;

let rec collect f = function
    | [] -> []
    | x::xs -> f x @ collect f xs;;

(** List.rev: 'a list -> 'a list**)
let rec fNRev = 
    function
    | [] -> []
    | x::xt -> fNRev xt @ [x];;
let rec fRev xs acc =
    match xs with
    | [] -> acc
    | x::xt -> fRev xt (x::acc)
(* Applications of list functions. *)
(*** insert element to a list to be a set, Set.add ***) 
let insert x ys = 
    if List.contains x ys 
    then ys 
    else x::ys;;

(** union of two set 
**)
let union xs ys = 
    List.foldBack insert xs ys;;
union [1;2;3] [2;3;4;5]

(** disjoint relation of two list **)
let fDisjoint xs ys = 
    List.forall (fun X -> 
            List.forall (fun Y -> X<>Y) ys) xs;;

let pDisjointP s1 s2 = 
    pForAll (fun e1 -> 
        not (pExists (fun e2 ->
            e1=e2) s2)) s1;;

(** subset relation of two list **)
let fSubset xs ys = 
    List.forall (fun X -> 
        List.exists (fun Y -> X=Y) ys) xs;;

(** intersection of two list **)
let fInter xs ys = 
    List.filter (fun X -> 
            List.exists (fun Y -> X=Y) ys) xs;;


(* Set 
type Set<'a> = Head of 'a
             | Tail of Set <'a>
*)
(** Set.ofList: 'a list -> Set<'a> **)
let rec fOfList sc =
    function
    | [] -> Set.empty
    | x::xt -> Set.add x sc;;

(** Set.toList: Set<'a> -> 'a list **)
(** Set.toList: 'a -> Set<'a> -> Set<'a> **)
(** Set.remove: 'a -> Set<'a> -> Set<'a> **)
(** Set.contains: 'a -> Set<'a> -> bool **)
(** Set.isSubset: Set<'a> -> Set<'a> -> bool **)
(** Set.minElement: Set<'a> -> 'a  minimum element among set {a_1,...,a_n} where n>0**)
(** Set.maxElement: Set<'a> -> 'a **)
(** Set.count: Set<'a> -> int **)
(** Set.union: Set<'a> -> Set<'a> -> Set<'a> **)
(** Set.intersect: Set<'a> -> Set<'a> -> Set<'a> **)
(** Set.difference: Set<'a> -> Set<'a> -> Set<'a> **)
(** Set.filter: Set<'a> -> Set<'a> -> Set<'a> **)
(** Set.exists: ('a->bool) -> Set<'a> -> bool **)
(** Set.forall: ('a->bool) -> Set<'a> -> bool **)
(** Set.map: ('a->'b) -> Set<'a> -> Set<'b> **)
(** Set.fold: ('a->'b->'a) -> 'a -> Set<'b> -> 'a **)
(** Set.foldBack: ('a->'b->'b) -> 'b -> Set<'a> -> 'b **)


(** insertion sort **)
let rec fOInsert  x ys =
    match ys with
    | [] -> [x]
    | y::_ when x<y -> x::ys
    | y::yt -> y::fOInsert x yt;;

fOInsert 1 [0;2;3;4];;

let rec fInsort(xs) =
    match xs with
    | [] -> []
    | x::xt -> fOInsert x (fInsort xt);;

fInsort([1;2;3;4;0]);;

(*** merge : A list -> A list -> A list
merge [1;4;9;12] [2;3;4;5;10;13] = [1;2;3;4;4;5;9;10;12;13]

Invariant: 
input lists should be ordered 
Assumption for function merge xs ys:
xs and ys are ordered lists.
***)
let rec merge xs ys =
    match (xs,ys) with
    | ([], _) -> ys
    | (_, []) -> xs
    | (X::xt, Y::yt) -> if X<=Y 
                        then X::merge xt ys
                        else Y::merge xs yt;;

(*** split: A list -> A list*A list 
***)
let rec split = 
    function
    | [] -> ([],[])
    | [x] -> ([x],[])
    | x0::x1::xt -> let (AN,BN) = split xt
                    (x0::AN,x1::BN);;
split [1;2;3;4;5];;

(*** sort: A list -> A list 
We can recursively apply split * merge functions to the input list. Empty list and singleton list would be trivial bind to itself trivially.
***)
let rec sort xs =
    match xs with
    | [] -> []
    | [X] -> [X]
    | _ -> let (YS,ZS) = split xs
           merge (sort YS) (sort ZS);;

sort [7;4;1;2;0;6;7;5;3];;

(* Map 
type Map<'a,'b> = Head of ('a,'b)
                | Tail of Map <'a,'b> 
*)
(** Map.ofList: ('a*'b) list -> Map<'a,'b> **)
(** Map.toList: Map<'a,'b> -> ('a,'b) list**)
(** Map.add: ('a,'b) -> Map<'a,'b> -> Map<'a,'b> **)
(** Map.containsKey: 'a-> Map<'a,'b> -> bool **)
(** Map.find: 'a -> Map<'a,'b> -> 'b **)
(** Map.tryFind: 'a -> Map<'a,'b> -> 'b option **)
(** Map.filter: 'a -> Map<'a,'b> -> Map<'a,'b> **)
(** Map.exists: ('a->bool) -> Map<'a,'b> -> bool **)
(** Map.forall: ('a->bool) -> Map<'a,'b> -> bool **)
(** Map.map: ('b->'c) -> Map<'a,'b> -> Map<'a,'c> **)
(** Map.fold: ('a->'b->'c->'a) -> 'a -> Map<'b,'c> -> 'c **)
(** Map.foldBack ('a->'b->'c->'c) -> Map<'a,'b> -> 'c -> 'c **)

(* Multiset:
type MultisetMap<'a when 'a : comparison> = Map<'a,int>
type Multiset<'a when 'a : equality> = ('a * int) list
*)