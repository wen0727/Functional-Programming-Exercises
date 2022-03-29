#time
(* Three version of factorial funcitons *)
let rec fact =
    function
    | 0 -> 1
    | n when n>0 -> n * fact (n-1)
    | _ -> failwith "n must be not negative integer.";;
(* the accumulating parameter x must be feed with 1 *)
let rec factA x =
    function
    | 0 -> x
    | n when n>0 -> factA (n*x) (n-1)
    | _ -> failwith "n must be not negative integer.";;
(* when n is zero, the value is the identity of the multiplication *)
let rec factC c = 
    function
    | 0 -> c 1
    | n when n>0 -> factC (fun x -> c (x*n)) (n-1)
    | _ -> failwith "n must be not negative integer.";;

factC id 5;;

(* Model of binary trees *)
type BinTree<'a> = | Leaf
                   | Node of BinTree<'a> * 'a * BinTree<'a>;;

(* function of binary tree 
    countA: int -> BinTree<'a> -> int
*)
let rec countA acc = 
    function
    | Leaf -> acc
    | Node(tl,_,tr) -> let nacc = countA (acc+1) tl 
                       countA (nacc) tr;;

let t3 = Node(Node(Leaf, -3, Leaf), 0, Node(Leaf, 2, Leaf));;
let t4 = Node(t3, 5, Node(Leaf, 7, Leaf));;

countA 0 t4;;

(* Non-tail recursive version of tree counting function. *)
let rec count =
    function
    | Leaf -> 0
    | Node(tl,_,tr) -> 1 + count tl + count tr;;

(* Continuation-based tail recursive counting function. *)
let rec countC c =
    function
    | Leaf -> c 0
    | Node(tl,_,tr) -> countC (fun nl -> countC (fun nr -> c(nr+nl+1)) tr) tl;;

(* A tail-recursive function for counting nodes of binary tree 
with accumulating parameter and continuation-based method *)
let rec countAC acc c =
    function
    | Leaf -> c 0
    | Node(tl,_,tr) -> let nl = countA acc tl
                       countAC acc (fun nr -> c(nl+nr+1)) tr;;

(* A balanced tree generator *)
let rec genTree xs =
    match xs with
    | [| |]   -> Leaf     //array
    | [| x |] -> Node(Leaf,x,Leaf)
    | _       -> let m = xs.Length / 2
                 let xsl = xs.[0..m-1]
                 let xm = xs.[m]
                 let xsr =xs.[m+1 ..]
                 Node(genTree xsl,xm,genTree xsr);;

(* Generating an left unbalanced tree *)
let rec genLTree xs =
    match xs with
    | [| |]   -> Leaf     //array
    | [| x |] -> Node(Leaf,x,Leaf)
    | _       -> let m = xs.Length 
                 let xsl = xs.[0..m-1]
                 let xm = xs.[m]
                 Node(genTree xsl,xm,Leaf);;

let rec genRTree xs =
    match xs with
    | [| |]   -> Leaf     //array
    | [| x |] -> Node(Leaf,x,Leaf)
    | _       -> let m = xs.Length 
                 let xsr = xs.[0..m-1]
                 let xm = xs.[m]
                 Node(Leaf,xm,genRTree xsr);;

(* testing of balanced tree *)
let fTreeN n = genTree [| 1..n |];;
let expT1 = fTreeN 20000000;;
countA 0 expT1;;    // 1/3
count expT1;;       // 1/2
countC id expT1;;   // 1
countAC 0 id expT1;; // less than 1/3

(* testing of left unbalanced tree *)
let fLTreeN n = genTree [| 1..n |];;
let expT2 = fLTreeN 20000000;;
countA 0 expT2;;    // 1/3
count expT2;;       // 1/2
countC id expT2;;   // 1
countAC 0 id expT2;; // less than 1/3

(* testing of right unbalanced tree *)
let fRTreeN n = genTree [| 1..n |];;
let expT3 = fRTreeN 20000000;;
countA 0 expT3;;    // 1/3
count expT3;;       // 1/2
countC id expT3;;   // 1
countAC 0 id expT3;; // less than 1/3


(* Search tree invariant(property) 
    every node (tl,v,tr) satisfies
    vl < v for every value v1 in tl and
    vr > v for every value vr in tr
*)
(* balanced tree, median value is the root *)
(* function of adding/inserting a value to a search tree *)
let rec addTree x t =
    match t with
    | Leaf -> Node(Leaf,x,Leaf)
    | Node(tl,v,tr) when x<v -> Node(addTree x tl,v,tr)
    | Node(tl,v,tr) when x>v -> Node(tl,v,addTree x tr)
    | _ -> t;;
(* compare to list, searching value is O(n), searching in a 
balanced tree is  O(logn). When the number of nodes is getting 
larege the efficiency of balanced tree is significant. *)

(* Consider following function *)
let rec f n =
    function
    | 0          -> 1
    | k when k>0 -> n*(f n (k-1))
    | _          -> failwith "illegal argument";;
(* Make a tail-recursive version of f using an accumulating parameter *)
let rec fA acc n =
    function
    | 0 -> acc
    | k when k>0 -> fA (n*acc) n (k-1)
    | _ -> failwith "illegal argument";;
(* The initial accumulating parameter must be multiplicative identity *)

(* Declare a continuation-based tail-recursive version of f *)
let rec fC c n =
    function
    | 0 -> c 1
    | k when k>0 -> fC (fun x -> c(x*n)) n (k-1)
    | _ -> failwith "illegal argument";;

(* Consider following functions *)
let rec f13 i = 
    function
    | []    -> []
    | x::xs -> (i,x)::f13 (i*i) xs;;

type 'a Tree = | Lf
               | Br of 'a Tree * 'a * 'a Tree;;

let rec g p = 
    function 
    | Lf                  -> None
    | Br (_,a,t) when p a -> Some t
    | Br (t1,a,t2)        -> match g p t1 with
                             | None -> g p t2
                             | res  -> res;;
(* type 'a option = None | Some of 'a *)
(* Analysis of the functions f and g *)
(* f13 
    1. The argument of the function can be labeled with fresh
    types as below:
        i : T1  arg1 : T2

    2. The pattern expressions can be labeled as:
        [] : T3 list    x::xs : T3 list     x: T3   xs: T3 list

    3. The value expressions can be labeled as:
        [] : T4 list    (i,x)::f (i*i) xs : T4 list     (i,x) : T4

    4. We can unify the types as:
        T1 = int 
        T2 = T3 list 
        T4 = int*T3 

    5. In F#, the types a renamed as
        T2 = T3 list = 'a list
        T4 = (int*'a) list
       The most general type of f is
        f13: i:int -> 'a list -> (int*'a) list

    g
     1. The arguments of the function can be labeled with fresh
     types such as:
        p : T1      arg1 : T2

     2. The pattern expressions can be labeled as below:
        Lf : T3 Tree
        Br(_,a,t) : T3 Tree     a : T3   T : T3 Tree
        Br(t1,a,t2) : T3 Tree  t1 : T3 Tree t2 : T3 Tree
        p : T3 -> bool

     3. The value expressions can be labeled as below: 
        None : T4 option
        Some t : T4 option
        res : T4 option 

     4. We can unify the types as 
        T2 = T4 = T3 Tree

     5. In F#, the types can be renamed as
        T2 = T4 = T3 Tree = 'a Tree

        The most general type of g
        g: p:('a -> bool) -> 'a Tree -> 'a Tree option

    What are the functions compute>
    f13
     The function computes list of base i power of 2 power of n paired with 
     elment in a list.
        i0 = i  = i^(2^0)
        i1 = i0^2 = i^(2^1)
        i2 = i1^2 = i^(2^2)

        ...
        in= in-1 ^2 = i^(2^n)

    g
      when the 
     The function traverses right sub-trees untill leaf to compute 
     the right-subtree which the matching pattern's node value
     satisfies the predicate p.
*)
(* Make a tail-recursive variant of f13 with accumulating parameter. *)
let rec f13A acc i =
    function
    | [] -> List.rev acc
    | x::xs -> f13A ((i,x)::acc) (i*i) xs;;

(* Make a continuation-based tail-recursive version of f13 *)
let rec f13C c i =
    function
    | [] -> c []
    | x::xs -> f13C (fun ys -> c((i,x)::ys)) (i*i) xs;;
(* Pros and cons
    Accumulationg parameter version is most efficient regarding to time.
    Continuation-based version is most efficient regarding stack size.
*)

(* Consider the following functions g1 *)
let rec g1 p =
    function
    | x::xs when p x -> x::g1 p xs
    | _ -> [];;

(* make a continuation-based tail-recursive variant of g1 *)
let rec g1C c p =
    function
    | x::xs when p x -> g1C (fun ys -> c(x::ys)) p xs
    | _ -> c [];;

(* Consider the following functions 
Recall the type 'a Tree
type 'a Tree = | Lf
               | Br of 'a Tree * 'a * 'a Tree;;
*)
type 'a Tree11 = | Lf
                 | Br of 'a * 'a Tree11 * 'a Tree11;;
let rec f11(n,t) = 
    match t with 
    | Lf          -> Lf
    | Br(a,t1,t2) -> if n>0 
                     then Br(a,f11(n-1,t1),f11(n-1,t2))
                     else Lf;;

let rec g11 p = 
    function
    | Br(a,t1,t2) when p a -> Br(a,g11 p t1,g11 p t2)
    | _                    -> Lf;;

let rec h k = 
    function
    | Lf -> Lf
    | Br(a,t1,t2) -> Br(k a,h k t1,h k t2);;

(* Analysis of the functions f11, g11 and h *)
(*
   f11
    1. The arguments of the function can be labeled with 
    fresh types as:
        (n,t) : T1      n : T2      T : T3

    2. The pattern expressions can be labled as below:
        Lf : T4 Tree11
        Br(a,t1,t2) : T4 Tree11
        a : T4          t1 : T4 Tree11        t2 : T4 tree11

    3. The value expression can be labled as below:
        Lf : T4 Tree11
        Br(a,f11(n-1,t1),f11(n-1,t2)) T4 Tree11
        f11: int*T4 Tree11 -> T4 Tree11
    
    4. We can unify the types as:
        T1 = int* T4 Tree11
        T2 = int
        T3 = T4 Tree11

    5. In F#, the types can be renamed as:
        T4 = 'a

       The function f11 has most general type as:
        f11: int*'a Tree11 -> 'a Tree11

   g11
    1. The arguments of the function can be labeled with fresh 
    types as:
        p : T1       arg1 : T2

    2. The wild card pattern matches the Tree11 type which the 
    node value does not satisfies predicate p or leaf. 
    The pattern expressions can be labeled as:
        Br(a,t1,t2) : T3 Tree11
        a : T3      t1 : T3 Tree11      t2 : T3 Tree11
        p : T3 0 -> bool

    3. The value expressions can be labeled as:
        Br(a,g p t1,g p t2) : T3 Tree11
        Lf : T3 Tree11

    4. We can unify the types as:
        T2 = T3 Tree11

    5. In F# the types can be renamed as:
        T3 = 'a
       The most general type of g11
        g11: p: ('a -> bool) -> 'a Tree11 -> 'a Tree11

   h 
    1. The argumetns of the function can be labeled with fresh
    types such as:
        k : T1      arg1 : T2
    
    2. The pattern expressions can be labeled as:
        Lf : T3 Tree11      
        Br(a,t1,t2) : T3 Tree11
        a : T3 Tree11   t1 : T3 Tree11  t2 : T3 Tree11

    3. The value expressions can be lableled as:
        Lf : T4 Tree11
        Br(k a,h k t1,h k t2) : T4 Tree11
        k: T3 -> T4
        h k t1 : k:(T3 -> T4) -> T3 Tree11 -> T4 Tree11

    4. We can unify the types as 
        T2 = T3 Tree11

    5. In F#, the types are renamed as
        T3 = 'a
        T4 = 'b
       The most general type of h 
        h: k:('a->'b) -> 'a Tree 11 -> 'b Tree11

    What the functions computes?
    f11 
     The function trim the tree untill the node value
     is larger than 0.
        
    g11
     The function traverses the tree and replace nodes to leaf
     if the nodes value doesn't satisfy the predicate.

    h 
     The function converts the tree to a new type of tree.
*)