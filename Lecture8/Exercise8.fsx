(* Simple expressions is modeled as following, i.e. 1 + 2 * 3 *)
type exp = | C of int
           | BinOp of exp * string * exp;;

(* 1. Examples of exp *)
let eg1 = C 1;;
let eg2 = BinOp (C 1, "+", BinOp (C 2, "*", C 3));;
let eg3 = BinOp (BinOp (C 1, "+", BinOp (C 2, "*", C 3)), "-", BinOp (C 1, "+", BinOp (C 2, "*", C 3)));;

(* 2. Expression to string *)
let rec toString =
    function
    | C n -> string n
    | BinOp (e1,op,e2) -> "(" + toString e1 + op + toString e2 + ")";;

toString eg3;;

(* 3. Extract the set of operators from an expression. *)
let rec fExtractOp os =
    function
    | C _ -> os
    | BinOp (e1,op,e2) -> let tl = fExtractOp (Set.add op os) e1
                          fExtractOp tl e2;;

(* Expansion of the expression type. *)
type expE = | C of int
            | BinOp of expE * string * expE
            | Id of string
            | Def of string * expE * expE;;

(* 4. isDef: exp -> bool predicates whether an expression is defined. *)
let rec pDefVar vs =
    function
    | C _ -> true
    | BinOp (e1,_,e2) -> pDefVar vs e1 && pDefVar vs e2
    | Id x -> List.exists (fun y -> y=x) vs
    | Def (v,c,e) -> pDefVar vs c && pDefVar (v::vs) e;;

let isDef exp = pDefVar [] exp;;
let e4 = Def("x", C 8, Def("y", C 9, BinOp(Id "y","+",Id "x")));;
isDef e4;;

(* Model of rivers is represended by
    name of the river, 
    average stream flow rate 
    and list of tributaries.
   A tributary is also a river.
   River names are assumed to be unqique.
*)
type Name = string
type Flow = int
type River = R of Name * Flow * Tributaries 
and Tributaries = River list

(* 1. Examples of river *)
let r1 = R("R1",5,[]);
let r4 = R("R4",2,[]);
let r2 = R("R2",15,[r4]);
let riv3 = R("R3",8,[]);
let riv = R("R",10,[r1;r2;riv3;]);

(* 2. function contains: Name -> River -> bool 
    contains n r is true iff the name of river is n or a tributary of r is named n.
let rec fTContains n =
    function
    | [] -> false
    | t::tt -> contains n t || fTContains n tt
and contains n =
    function
    | R(n1,_,_) when n1=n -> true
    | R(_,_,ts) -> fTContains n ts
*)

let rec contains n =
    function
    | R(n1,_,_) when n1=n -> true
    | R(_,_,ts) -> List.exists (contains n) ts;;
contains "R" riv;;

(* 3. function allNames r 
    returns all names contained in a river. Ordering is not required
*)
let rec fTNames ns =
    function
    | [] -> ns
    | t::tt -> fTNames (fRNames ns t) tt
and fRNames ns =
    function
    | R(n,_,ts) -> fTNames (n::ns) ts;;

let allNames r = fRNames [] r;;
allNames riv;;

(* 4. function totalFlow r 
    returns the total flow of the river
*)
let rec fTFlow =
    function 
    | [] -> 0
    | t::tt -> totalFlow t + fTFlow tt
and totalFlow =
    function
    | R(_,fr,ts) -> fr + fTFlow ts;;
totalFlow riv;;

(* 5. function mainSource: River -> (Name*Flow) 
    finds out the biggest flow rate in a river 

    fold
*)
let rec fTmain cm =
    function
    | [] -> cm
    | t::tt -> fTmain (fRmain cm t) tt
and fRmain (n1,fr1) =
    function
    | R(n,fr,ts) -> if fr1<fr
                    then fTmain (n,fr) ts
                    else fTmain (n1,fr1) ts;;
let mainSource (R(n,fl,ts)) = fTmain (n,fl) ts;;
mainSource riv;;

(* 6. function tryInsert: Name -> River -> River -> River option 
    the value of tryInsert n t r is some r' which represents if 
    the n is the name of river r then r' is the river with addition 
    of the tributary t in the list.

    If n is not a name in river r then the value is None.

    The function below using fold approch. 
let rec fTInsert n t ot =
    function 
    | [] -> ot
    | x::xt -> fTInsert n t ((fRInsert n t x)::ot) xt
and fRInsert n t =
    function
    | R(n1,fr,xs) -> if n=n1 
                     then R(n1,fr,t::xs)
                     else R(n1,fr,fTInsert n t [] xs);;
let tryInsert n t r =
    if contains n r 
    then Some (fRInsert n t r)
    else None;;
tryInsert "R4" (R("R5",30,[])) riv;;

*)

let rec fRInsert n t =
    function
    | R(n1,fr,xs) when n=n1 -> (Some (R(n1,fr,t::xs)))
    | R(n1,fr,xs) -> match fTInsert n t xs with
                     | None -> None
                     | Some ts -> Some (R(n1,fr,ts))
and fTInsert n t =
    function
    | [] -> None
    | x::xt -> match fRInsert n t x with
               | None -> match fTInsert n t xt with
                         | None -> None
                         | Some ts -> Some (x::ts)
               | Some r -> Some (r::xt);; 
let tryInsert n t r = fRInsert n t r;;
tryInsert "R4" (R("R5",30,[])) riv;;

(* 7. Limitation of the model. 
    The model can't represent two mergig of two tributaries. 
    To solve the problem we could use DAG. 
*)