(* Knights and Knaves puzzle from the logician R.Smullyan *)
(* Part 1: Abstract syntax *)
type Prop<'a> = 
    | A of 'a
    | Dis of Prop<'a> * Prop<'a>
    | Con of Prop<'a> * Prop<'a>
    | Neg of Prop<'a>
    | Imp of Prop<'a> * Prop<'a>
    | BImp of Prop<'a> * Prop<'a>;;

(* Semantics 
    sem p asg = true    iff asg |= p holds
    sem: Prop<'a> -> Set<'a> -> bool
*)
let rec sem p asg =
    match p with
    | A a         -> Set.contains a asg
    | Dis(p1,p2)  -> sem p1 asg || sem p2 asg
    | Con(p1,p2)  -> sem p1 asg && sem p2 asg
    | Neg p1      -> not (sem p1 asg)
    | Imp(p1,p2)  -> sem (Neg p1) asg || sem p2 asg
    | BImp(p1,p2) -> (sem p1 asg && sem p2 asg) || (sem (Neg p1) asg && sem (Neg p2) asg);;//sem (Imp(p1,p2)) asg && sem (Imp(p2,p1)) asg //(sem p1 asg && sem p2 asg) || (sem (Neg p1) asg && sem (Neg p2) asg);;

(* Part 2: Negation Normal Form *)
let rec toNnf p =
    match p with
    | A _         -> p
    | Dis(p1,p2)  -> Dis(toNnf p1,toNnf p2)
    | Con(p1,p2)  -> Con(toNnf p1,toNnf p2)
    | Neg p1      -> match p1 with
                     | A _ -> p
                     | Dis(p2,p3)  -> Con(toNnf (Neg p2),toNnf (Neg p3))
                     | Con(p2,p3)  -> Dis(toNnf (Neg p2),toNnf (Neg p3))
                     | Neg p2      -> toNnf p2
                     | Imp(p2,p3)  -> Con(toNnf p2,toNnf (Neg p3))
                     | BImp(p2,p3) -> Con(toNnf (Neg (Con(p2,p3))),toNnf (Neg (Con(Neg p2,Neg p3))))
    | Imp(p1,p2)  -> Dis(toNnf (Neg p1),toNnf p2)
    | BImp(p1,p2) -> Dis(Con(toNnf p1,toNnf p2),Con(toNnf (Neg p1),toNnf (Neg p2)));;

(* Correctness of toNnf 
    onNnf: Prop<'a> -> bool
*)
let rec onNnf p =
    match p with
    | A _         -> true
    | Dis(p1,p2)  -> onNnf p1 && onNnf p2
    | Con(p1,p2)  -> onNnf p1 && onNnf p2
    | Neg p1      -> match p1 with
                     | A _ -> true
                     | _   -> false
    | Imp(_,_)  -> false
    | BImp(_,_) -> false;;

#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"
open FsCheck

let pCorrectNnf1 (p:Prop<string>) = onNnf (toNnf p);;
let _ = Check.Quick pCorrectNnf1;;
let _ = Check.Verbose pCorrectNnf1;;
(* A type for testing, to limit the randomness of string type *)
type Finite = Honest | Dishonest 

let pCorrectNnf2 (p:Prop<Finite>) = onNnf (toNnf p);;
let _ = Check.Quick pCorrectNnf2;;
let _ = Check.Verbose pCorrectNnf2;;

let pCorrectSem (p:Prop<Finite>) (asg:Set<Finite>) = 
    sem p asg = sem (toNnf p) asg;;
let _ = Check.Quick pCorrectSem;;
let _ = Check.Verbose pCorrectSem;;

(* Part3: Disjunctive Normal Form 
    literal     atom or negation of an atom
    elementary conjunciton      conjunction of literals
    transform a proposition in negation normal form to an
    equivalent propostion in DNF by the distributive laws.
*)
let rec dnf p =
    match p with
    | A _ -> p
    | Dis(p1,p2) -> Dis(dnf p1,dnf p2)
    | Con(p1,p2) -> match (dnf p1,dnf p2) with  //traversing tree
                    | (_,Dis(q1,q2)) -> Dis(dnf(Con(p1,q1)),dnf(Con(p1,q2)))
                    | (Dis(q1,q2),_) -> Dis(dnf(Con(q1,p2)),dnf(Con(q2,p2)))
                    | _ -> p
    | Neg _      -> p
    | _          -> failwith "The proposition hasn't been transformed to NNF previously.";;

(* A function toDnf to transfprms a proposition to DNF *)
let toDnf p = dnf (toNnf p);;

(* Check a proposition for whether it is in DNF *)
let rec onDnf p =
    match p with
    | A _ -> true
    | Dis(p1,p2) -> onDnf p1 && onDnf p2
    | Con(p1,p2) -> match (p1,p2) with
                    | (_,Dis(_,_)) | (Dis(_,_),_) -> false
                    | _ -> onDnf p1 && onDnf p2
    | Neg p1     -> match p1 with
                    | A _ -> true
                    | _ -> false
    | _ -> failwith "The proposition hasn't been transformed to NNF previously.";;

let pCorrectDnf (p:Prop<Finite>) (asg:Set<Finite>)= 
    onDnf (toDnf p) && sem p asg = sem (toDnf p) asg;;
let _ = Check.Quick pCorrectDnf;;
let _ = Check.Verbose pCorrectDnf;;

(* Part 4: Satisfying assignments 
    inconsistent      atom a and negation of atom a both 
    exists in a literal (elementary conjunction)
*)
(* Make a function ecTolist to extract list of literals 
    sequence
    duplication does not matter
*)
let rec ecToList acc p =
    match p with
    | A _        -> [p]::acc
    | Dis(p1,p2) -> let tl = ecToList acc p1
                    ecToList tl p2
    | Con(p1,p2) -> let tl = ecToSlist [] p1
                    (ecToSlist tl p2)::acc
    | Neg _      -> [p]::acc
    | _          -> failwith "The proposition hasn't been transformed to DNF previously."
and ecToSlist acc p =
    match p with
    | A _        -> p::acc
    | Con(p1,p2) -> let tl = ecToSlist acc p1
                    ecToSlist tl p2
    | Neg _      -> p::acc
    | _          -> failwith "The proposition hasn't been transformed to DNF previously.";;

(* Check the consistency of a list of literals. *)
let rec pConsisl =
    function
    | [] -> true
    | x::xt -> not (List.exists (fun y -> y=toNnf (Neg x)) xt) && pConsisl xt
    
let pConsisll ll = 
    List.forall (fun ls -> pConsisl ls) ll;;
(* Make a function toEClists p to extract consistent literals *)
let toEClists p =
    List.filter (fun ls -> pConsisl ls) (ecToList [] (toDnf p));;

(* Add Imp constructor to the type for constructing the 
    implication. Note, implication is not in NNF by itself.
    Implication can be rewrited as
        A=>B -> -A \/ B 
    This can be add to the semantics.
    Try the function with following example and check manually.
    (-P => -Q) => (P => Q)
    (-Q => -P) => (P => Q)
*)
(*
    Manual Evaluation
        (-P => -Q) => (P => Q)
    =   (-(-P => -Q)) \/ (P => Q)
    =   (-(P\/-Q)) \/ (-P\/Q)
    =   (-P/\Q) \/ (-P\/Q)
    ~>[[Neg (A "P"); A "Q"]; [Neg (A "P")]; [A "Q"]]

        (-Q => -P) => (P => Q)
    =   (-(-Q => -P)) \/ (P => Q)
    =   (-(Q \/ -P)) \/ (-P \/ Q)
    =   (-Q /\ P) \/ (-P \/ Q)
    ~> [[Neg (A "Q"); A "P"]; [Neg (A "P")]; [A "Q"]]
*)
let eg1Imp = Imp(Imp(Neg(A "P"),Neg(A "Q")),Imp(A "P",A "Q"));;
let eg2Imp = Imp(Imp(Neg(A "Q"),Neg(A "P")),Imp(A "P",A "Q"));;
let s1Imp = toEClists eg1Imp;;
let s2Imp = toEClists eg2Imp;;

(* Part 5: Solving puzzles *)
(* Declare a type Inhabitant with three values to model 
    three people.
*)
type Inhabitants = K1 | K2 | K3;;
(* Make proposition for the following 
    k1 says: "All of us are knaves"
    k2 says: "Exactly one of us is knight"
*)
let k1 = Con(Neg(A K1),Con(Neg(A K2),Neg(A K3)));;
let k2 = Dis(Con(A K1,Con(Neg(A K2),Neg(A K3))),
            Dis(Con(Neg(A K1),Con(A K2,Neg(A K3))),
                Con(Neg(A K1),Con(Neg(A K2),A K3))));;
(* Add Bi-imp to the tree *)
(* Manual solution
    k1 := -K1 /\ -K2 /\ -K3  
    k2 :=  K1 /\ -K2 /\ -K3
       \/ -K1 /\  K2 /\ -K3
       \/  K1 /\ -K2 /\  K3 
      
    -K1
    
    asg |=  k1 <=> -K1 ?
    asg |=  k2 <=> K2 ?
*)
(* Form a recipe of the analysis above *)

let r1k1 = Neg(A K1);;
let puzzle1:Prop<Inhabitants> = 
    Con(r1k1,k2);;
    
    
let s1Puz = toEClists puzzle1;;

(* Make a proposition for the following 
    k1 mumbles
    k2 says: "k1 said he is a knave"
    k3 says: "k2 is lying"
*)
let ok2 = Neg(A K1);;
let ok3 = Neg(A K2);;
(* Manual solution
    ok2 := -K1 
    ok3 := -K2 

    if K2 is knight then K1 is knave            T   K2 -K1 
    if k2 is knight then K1 is not knave        F
    if K2 is not knight then K1 is knave        F
    if K2 is not knight then K1 is knight       T  -K2  K1  

    if K3 is knight then K2 is knave            T   K3 -K2  K1
    if K3 is knight then K2 is not knave        F   
    if K3 is not knight then K2 is knave        F  
    if K3 is not knight then K2 is not knave    T  -K3  K2 -K1   

*)

let r2ok1  = BImp(A K2, Neg(A K1))  
let r2ok2  = BImp(A K3, Neg(A K2))  
let puzzle0:Prop<Inhabitants> =
    Con(r2ok1,r2ok2);
let s2Puz0 = toEClists puzzle0;;

(* Part 6: Exponential blow-up of DNF 
    Boolean satisfiable problem SAT
    NP-complete problem, 
    nondeterministic polynomial complecity
    which is hard to decide.

    2^n possible assigment depends on n number of atoms.

    worst-case exponentional running time.
*)
(* Make a function badProp to generate CNF propositions *)
let rec badProp p = 
    function
    | 0 -> p
    | n when n>0 -> badProp (Con(p,(Dis(A("p",n),A("q",n))))) (n-1)
    | _ -> failwith "The argument must be not negative number."

(* Experience with the worst-case senarial of the 2^n *)
toEClists (badProp (Dis(A("p",0),A("p",0))) 2);;











