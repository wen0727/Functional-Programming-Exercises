(* P1 *)
type Person = string
type Contacts = Person list
type Register = (Person * Contacts) list
let reg1 = [("p1", ["p2"; "p3"]); ("p2", ["p1"; "p4"]);
            ("p3", ["p1"; "p4"; "p7"]); ("p4", ["p2"; "p3"; "p5"]);
            ("p5", ["p2"; "p4"; "p6"; "p7"]);
            ("p6", ["p5"; "p7"]); ("p7", ["p3"; "p5"; "p6"])];;
(** Q1 **)
let p1 x xs = List.forall (fun y -> y<>x) xs;;
let rec pInv1 p = 
    function
    | [] -> true
    | x::xt -> p x xt && pInv1 p xt;;

let invQ1 reg = List.forall (fun (_,ps) -> pInv1 p1 ps) reg;;

(** Q2 **)
let p2 (y,_) xs = List.forall (fun (p,_) -> y<>p) xs;;
let rec pInv2 p =
    function
    | [] -> true
    | (y,ys)::xt -> p (y,ys) xt && ys<>[] && pInv2 p xt;;
let invQ2 reg = pInv2 p2 reg;;

let rec insert p ps = if List.contains p ps then ps else p::ps
let rec combine ps1 ps2 = List.foldBack insert ps1 ps2;;

(** Q3 **)
let rec extractImm x =
    function
    | [] -> []
    | (y,ys)::zt -> if y=x
                    then ys
                    else extractImm x zt;;

(** Q4 **)
let rec addContact p1 p2 reg =
    match reg with
    | [] -> reg
    | (y,ys)::zt -> if y=p1
                    then (y,insert p2 ys)::zt
                    else (y,ys)::addContact p1 p2 reg;;

(** Q5 **)
let rec extractCon p reg =
    match reg with
    | [] -> []
    | (y,ys)::zt -> if y=p
                    then List.fold (fun acc x -> combine acc (extractImm x reg)) ys ys
                    else extractCon p zt;;
extractCon "p1" reg1



(* P3 *)
type Name = string;;
type Part = | S of Name // Simple part
            | C of Name * Part list;; // Composite part
(** Q1 **)
let rec pNEmpty = 
    function
    | S _ -> true
    | C (_,ps) -> ps <> [] && 
                  List.forall (fun x -> pNEmpty x) ps;;

(** Q2 **)
let maxInt x y =
    if x>y 
    then x 
    else y;;
let rec maxL =
    function
    | [] -> 0
    | [x] -> x
    | x::y::zs -> maxL (maxInt x y::zs);;
let rec depthPart =
    function
    | S n -> 0
    | C (n,ps) -> 1 + maxL(List.map (fun x -> depthPart x) ps);; 
let cp1 = C ("1", [S "1.-"; C ("1.1",[
                                      C ("1.1.1",[
                                                  S "1.1.1.-"; C ("1.1.1.1", [
                                                                              S "1.1.1.1.-"]); 
                                                               C ("1.1.1.2", [
                                                                              S "1.1.1.2.-"])]); 
                                      C ("1.1.2", [
                                                   S "1.1.2.-"])]); 
                            C ("1.2", [S "1.2.-"])]);;
depthPart cp1;;

(** Q3 **)

(** Q4 **)
//m1
let rec addSP ns =
    function
    | S x -> insert x ns
    | C (_,ps) -> List.foldBack (fun y acc-> combine (addSP ns y) acc) ps ns;; 
addSP [] cp1

let rec countE =
    function
    | [] -> 0
    | x::xt -> 1 + countE xt;;

let nSP p = countE (addSP [] p);;
nSP cp1
//m2
let rec fnSP (n,sps) =
    function 
    | S x -> if not (List.contains x sps) 
             then (n+1,x::sps) 
             else (n,sps)
    | C (_,ps) -> List.fold (fun (u,v) p -> fnSP (u,v) p ) (n,sps) ps;;
fnSP (0,[]) cp1
let firstE (a,_) = a;;
let nnSP p = firstE(fnSP (0,[]) p);;
nnSP cp1

let rec fnCP (n,cps) =
    function
    | S _ -> (n,cps)
    | C (x,ps) -> if not (List.contains x cps) 
                  then List.fold (fun (u,v) p -> fnCP (u,v) p) (n+1,x::cps) ps
                  else List.fold (fun (u,v) p -> fnCP (u,v) p) (n,cps) ps

let nnCP p = firstE(fnCP (0,[]) p);;
fnCP (0,[]) cp1
nnCP cp1
//m1
let rec countCP =
    function
    | S _ -> []
    | C (_,ps) -> [countE ps] @ countPs ps
and countPs =
    function
    | [] -> []
    | x::xt -> countCP x @ countPs xt
//m2
let rec fcountCP = 
    function
    | S _ -> []
    | C (_,ps) -> List.foldBack (fun x acc -> fcountCP x @ acc) ps [countE ps]
countCP cp1
fcountCP cp1

let rec pLL = 
    function
    | [] -> true
    | x::xt -> (not (List.contains x xt)) && pLL xt;;
let checkLL p = pLL (fcountCP p);;
checkLL cp1
//m2

let isWF p = 
    depthPart p = 3 &&
    nnSP p = 5 &&
    nnCP p = 4 &&
    checkLL p

(** Q5 **)
let rec extractSP nl =
    function
    | S n -> n::nl
    | C (_,ps) -> List.foldBack (fun x acc -> extractSP acc x) ps nl;;
extractSP [] cp1;;

(** P4 **)
(** Q1 **)
let rec gC i k =
    if i=0 then k 0
    else if i=1 then k 1
         else gC (i-1) (fun v1 -> 
                gC (i-2) (fun v2 -> 
                    k(v1+v2)));;
gC 2 id
 Seq.initInfinite (fun i -> i)