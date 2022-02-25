module Polynomial

let fXorder =
    function
    | 0 -> ""
    | 1 -> "x"
    | n -> "x^"+ string n;;

let fTerm n = 
    function
    | 0 -> ""
    | 1 -> "+" + fXorder n 
    | c -> if c>1 then "+" + string c + fXorder n
           else string c + fXorder n

let rec fPRterm n = 
    function
    | [] -> ""
    | x::xt -> fTerm n x + fPRterm (n+1) xt;;
let rec fPFterm n = 
    function
    | [] -> ""
    | x::xt when x<>0 -> string x + fXorder n + fPRterm (n+1) xt
    | _::xt -> fPFterm (n+1) xt;;

let toString ts = fPFterm 0 ts;;

let rec fRemove0 xs = 
    match xs with
    | [] -> []
    | x::xt -> if x=0 
               then fRemove0 xt
               else List.rev xs;;

(* Customize the string function for type Poly. F# book Section 7.7 and slide 6 page 32. *)
type Poly = 
    | P of int list
    override p.ToString() =
        match p with
        | P xs -> toString xs;;

(* Part 1 source code. *)

let prune xs = P (fRemove0 (List.rev xs));;

let rec fAddP ss ts = 
    match (ss,ts) with
    | ([],_) -> ts
    | (_,[]) -> ss
    | (X::st,Y::tt) -> (X+Y)::fAddP st tt;;
let add (P p1) (P p2) = prune (fAddP p1 p2);;


let rec fMulCP c ts =
    match ts with
    | _ when c=0 -> []
    | [] -> []
    | X::tt -> (c*X)::fMulCP c tt;; 
let mulC c (P x) = prune (fMulCP c x);;

let rec fSubP ss ts =
    match (ss,ts) with
    | ([],Y::tt) -> -Y::fSubP [] tt
    | (_,[]) -> ss
    | (X::st,Y::tt) -> (X-Y)::fSubP st tt;;
let sub (P p1) (P p2) = prune (fSubP p1 p2)

let fMulXP ts =
    match ts with
    | [] -> []
    | _ -> 0::ts;;
let mulX (P ts) = prune (fMulXP ts);;

let rec fMulP ss ts =
    match (ss,ts) with
    | ([],_) -> []
    | (_,[]) -> []
    | (X::st,_) -> fAddP (fMulCP X ts) (fMulP st (fMulXP ts));;
let mul (P p1) (P p2) = prune (fMulP p1 p2);;

let rec fEvalP s ts =
    match ts with
    | [] -> 0
    | X::tt -> X + fEvalP s (fMulCP s tt);;
let eval c (P ps) = fEvalP c (fRemove0 ps);;

(* Part 2 source code. *)
let rec isLegal xs = 
    match xs with
    | [] -> true
    | [X] -> X<>0 
    | _::xt -> isLegal xt;;

let rec derivativeH = 
    function
    | (_,[]) -> []
    | (n,x::xt) -> if n=0 then derivativeH(n+1,xt)
                   else (x*n)::derivativeH(n+1,xt);;
let derivative (P ts) = prune (derivativeH(0,ts));;

let rec powerP ps = 
    function
    | 0 -> [1]
    | n -> let NP = powerP ps (n-1)
           fMulP ps NP;;

let rec fPsubst ps n qs =
    match ps with
    | [] -> []
    | X::pt -> let NP = fPsubst pt (n+1) qs
               fAddP (fMulCP X (powerP qs n)) NP;;
let compose (P p1) (P p2) = prune (fPsubst p1 0 p2);;

(* Part 4 source code. *)
[<CustomEquality;CustomComparison>]
type Degree = 
    | MinusInf
    | Fin of int
    interface System.IComparable with
        member d1.CompareTo dobj =
            match d1 with
            | MinusInf -> match dobj with 
                          | :? Degree as d2 -> match d2 with
                                               | MinusInf -> 0
                                               | Fin n -> -1
                          | _ -> failwith "dobj cannot compare values of different types" 
            | Fin n1 -> match dobj with 
                        | :? Degree as d2 -> match d2 with
                                             | MinusInf -> 1
                                             | Fin n2 -> compare n1 n2
                        | _ -> failwith "dobj cannot compare values of different types"         
    override d1.Equals dobj =
        match d1 with 
        | MinusInf -> match dobj with
                      | :? Degree as d2 -> match d2 with
                                           | MinusInf -> true
                                           | Fin n -> false
                      | _ -> failwith "dobj cannot compare values of different types"  
        | Fin n1 -> match dobj with
                    | :? Degree as d2 -> match d2 with
                                         | MinusInf -> false
                                         | Fin n2 -> n1=n2
                    | _ -> failwith "dobj cannot compare values of different types"  
    override d.GetHashCode() = hash d
    override d.ToString() =
        match d with
        | MinusInf -> "MinusInf"
        | Fin n -> if n>=0 then "Fin " + string n
                   else "n must be not negative number"

let rec p2Deg = 
    function
    | [] -> 0
    | _::pt -> 1 + (p2Deg pt);;
              
let fDegreeP ps = 
    match ps with
    | [] -> MinusInf
    | _::pt -> Fin (p2Deg pt);;
let degree (P xs) = fDegreeP xs;;

let addD d1 d2 = 
    match (d1,d2) with
    | (MinusInf,_) | (_,MinusInf) -> MinusInf
    | (Fin N,Fin M) -> Fin (N+M);;


(* Part 6 source code. *)
let ofList xs = prune xs;;
let toList (P ps) = ps;;
let ofArray ar = prune (List.ofArray ar);;

type Poly with
    static member ( + ) (P p1, P p2) = add (P p1) (P p2)
    static member ( - ) (P p1, P p2) = sub (P p1) (P p2)
    static member ( * ) (c, P xs) = mulC c (P xs)
    static member ( * ) (P p1, P p2) = mul (P p1) (P p2)

type Degree with
    static member (+) (d1, d2) = addD d1 d2

