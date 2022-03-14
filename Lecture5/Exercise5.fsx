(* Exercise 5 *)

(** Exercise from lecture slide 5. **)
(*** unzip functions, unzip: ('a*'b) list -> 'a list*'blist 

let h (x,y) (xs,ys) = (x::xs,y::ys)
let rec unzip1 = function
                 | []         -> ([],[])
                 | (x,y)::xys -> h (x,y) (unzip1 xys);;
let rec unzip2 = function
                 | []         -> ([],[])
                 | (x,y)::xys -> let (xs,ys) = unzip2 xys
                                 (x::xs,y::ys);;
***)

let fUnzipS xys = 
    List.foldBack (fun (X,Y) (xs,ys) ->
        (X::xs,Y::ys)) xys ([],[]);;

(*** Declare functions in HR on page 87 :
        "areNb c1 c2 m"
        "canBeExtBy"
        "extColouring m cols c"
        "countries"
        "colCntrs m cs"
     by using "Set" library function. 
***)
let fAreNbS c1 c2 m =
    Set.contains (c1,c2) m || 
        Set.contains (c2,c1) m;;

let fCanBeExtByS m col c = 
    Set.forall (fun X -> 
        fAreNbS X c m) col;;

let rec fExtColoringS m cols c =
    if Set.isEmpty cols             
    then Set.singleton (Set.singleton c)
    else let col = Set.minElement cols
         let cols' = Set.remove col cols
         if fCanBeExtByS m col c
         then Set.add (Set.add c col) cols'
         else Set.add col (fExtColoringS m cols' c);;
(* Comment: The use of Set library function is worse than pattern matching. *)

let fCountriesS m = 
    Set.fold (fun cs (C1,C2) -> 
        Set.add C1 (Set.add C2 cs)) Set.empty m;;
let fCountriesSf m = 
    Set.foldBack (fun (C1,C2) cs ->
        Set.add C1 (Set.add C2 cs)) m Set.empty;;

let fColCntrS m cs = 
    Set.foldBack (fun C cols -> 
        fExtColoringS m cols C) cs Set.empty;;

let fColMap m =
    fColCntrS m (fCountriesS m);;

(*** Lecture 5 slide page 27,
        what is f?
    f can be defined as following annonyous function in the parenthesis.
***)
let fAcodeM reg = 
    Map.foldBack (fun K (_,P) acc -> 
        (K,P)::acc) reg [];;


(***  Lecture 5 slide page 33,
    let f1(x,y) = match x with 
                  | 0 -> y
                  | _ -> -y;;
    Define equivalent version f2 by using function.
    Define curried version f3 by using match.
    Define curried version f4 by using function.
    
    let f2 = 
        function
        | (0,y) -> y
        | (_,y) -> -y;;

    let f3 x y =
        match x with
        | 0 -> y
        | _ -> -y;;

    let f4 y =
        function
        | 0 -> y
        | _ -> -y;;
***)

(**  homewors **)
(*** 1. Revise your solution of the simple company club problem 
(Week 37) using sets and maps whenever that is appropriate.
***)

#load "..\Lecture3\Exercise3.fsx"
open Exercise3
(**** 2. Declare predications p1 p2 by using library functions. ****)
let p1 (_,yb,ths) = 
    yb > 1982 && 
    List.exists (fun X -> 
        X="soccer") ths &&
    List.exists (fun X -> 
        X="jazz") ths;;
let p2 (_,yb,ths) =
    yb > 1982 && 
    List.exists (fun X -> 
        X="soccer") ths ||
    List.exists (fun X -> 
        X="jazz") ths;; 
(**** 3. Declare a function: 
            extractTargetGroup p r 
        that gives a list with names and phone numbers of the members from a club who satisfies the predication.
****)
let fFindNameNoL p r =
    List.foldBack (fun (n,(no,yb,ths)) nn ->
        if p (no,yb,ths) then (n,no)::nn
        else nn) r [];;
let extractTargetGroup p r = fFindNameNoL p r;;

(*** 2. Problem 1, questions 6 from Exam fall 2013 
        The question is to represent multisets by immutable maps. The representation of a multiset ms invariant: 
            the multiplicity n of each entry (e,n) of ms satisfies n>0.
        Give new declarations for functions :
            inv,insert and union by using map representation.
***)
type MultisetMap<'a when 'a : comparison> = Map<'a,int>;;
(**** inv:Multiset<'a> -> bool ****)
//Recursive function
let rec pForAll p xs = 
    match xs with
    | [] -> true
    | x::xt -> p x && pForAll p xt;;
let inv ms = 
    pForAll (fun (_,v)->
        v>0) (Map.toList ms);;

//Library Map.forall
let pInvM ms = 
    Map.forall (fun _ V -> 
        V>0) ms;;

(**** insert: 'a -> int -> Multiset<'a,int> -> Multiset<'a,int> ****)
//Recursive, since we need to convert map to list so the recursive function is quite similar to the one with the list representation. Therefore we can refer that one.
    
//Library Map. traverse the multiset twice.
let insert k v ms =
    Map.fold (fun acc a b ->
        if k=a then Map.add k (b+v) acc
        else acc) Map.empty ms;;

(**** union: Multiset<'a> ****)
let fOp2Int op =
    match op with
    | None -> 0
    | Some v -> v;;
let union msx msy =
    Map.foldBack (fun k v acc -> 
         Map.add k (v + fOp2Int (Map.tryFind k msy)) acc
        ) msx msy;;
let cXs = [('a',1);('b',2);('c',3)];;
let cYs = [('a',3);('b',4);('d',7)];;
union (Map.ofList cXs) (Map.ofList cYs);;
Map.add 'a' 1 (Map.ofList [('a',2)])

//maybe monad
type MM<'a> = 'a option;;

let retur a:MM<'a> = Some a;;

let (>>=) (mm:MM<'a>) (f:'a -> MM<'b>) = 
    match mm with
    | None-> None
    | Some v -> f v;;

Some 1 >>= (fun a -> Some (a+1))


(*** Problem 4 from summer 2015 exam. Make solution on paper first. ***)

type CourseNo = int
type Title = string
type ECTS = int
type CourseDesc = Title * ECTS
type CourseBase = Map<CourseNo, CourseDesc>

(**** 1. Declare a function isValidCourseDesc: CourseDesc -> bool 
        we require that valid ECTS points are positive integers that divisible by 5.
****)
let isValidCourseDesc (_,n) = 
    n>0 && n%5=0;;
(**** 2. Declare a function isValidCourseBse: CourseBase -> bool
        where it is true if every course description in course base is valid.
****)

let isValidCourseBase cb = pForAll isValidCourseDesc (Map.toList cb);;

let pIsValidCourseBaseH cb = 
    Map.forall (fun _ v -> 
        isValidCourseDesc v) cb;;

(**** 3. Declare a function disjoint: Set<'a> -> Set<'a> -> bool 
        where it is true if the two sets have no common elements.
****)
let rec pExists p xs =
    match xs with
    | [] -> false
    | x::xt -> p x || pExists p xt;;
let pDisjointP s1 s2 = 
    pForAll (fun e1 -> 
        not (pExists (fun e2 ->
            e1=e2) s2)) s1;;

let disjoint s1 s2 = pDisjointP (Set.toList s1) (Set.toList s2);;



let pDisjointH s1 s2 =
    Set.forall (fun e1 ->
        not (Set.exists (fun e2 ->
            e1=e2) s2)) s1;;
pDisjointH (Set.ofList [1]) (Set.ofList [1;2;3]);;

(**** 4. Declare a function sumECTS: Set<CourseNo> -> CourseBase -> int 
        where sumECTS cs cb is the sum of all ECTS points of the set of course numbers in the course base. 
****)
(* 
//Maybe monad version of map look up and addition of the value. 
let rec fLookUpMM cn cb = 
    match cb with
    | [] -> None
    | (a,b)::_ when cn=a -> retur b
    | _::ent -> fLookUpMM cn ent;; 
fLookUpMM 3 (Map.toList (Map.ofList [(1, Some 5); (2, Some 5)]));;

let rec fSumECTSMM cns cb =
    match cns with
    | [] -> Some 0
    | cn::cnt -> fLookUpMM cn cb >>= (fun a -> fSumECTSMM cnt cb >>= (fun b -> Some (a+b)));;
fSumECTSMM (Set.toList (set [1])) (Map.toList (Map.ofList [(1,Some 5); (2,Some 5); (3,Some 5); (4,Some 5)]));;
// *)
// Nomal look up and addtion of value 
let rec fLookUp cn cb = 
    match cb with
    | [] -> 0
    | (a,b)::_ when cn=a -> b
    | _::ent -> fLookUp cn ent;;

let rec fSumECTS cns cb =
    match cns with
    | [] -> 0
    | cn::cnt -> let a = fLookUp cn cb
                 let b = fSumECTS cnt cb
                 a+b;;
let rec sumECTS cns cb = fSumECTS (Set.toList cns) (Map.toList cb);;

// Higher order funcitons
let fsumECTSH cns cb =
    Set.foldBack (fun cn acc ->
        fOp2Int (Map.tryFind cn cb) + acc) cns 0;;

type Mandatory = Set<CourseNo>
type Optional = Set<CourseNo>
type CourseGroup = Mandatory * Optional


(**** 5 isValidCourseGroup: CourseGroup -> CourseBase -> bool 
            check whether a course group is valid for a given course base:
            1. man and opt courses are disjointed
            2. sum of ECTS of all man courses is <= 45
            3. opt courses is empty when ECTS of man = 45
                //Empty set is disjoint with every set, which means this is included in 1st predication. ECTS of man = 45 predication is covered in the 2nd predication by sum < or = 45.
            4. the sum of ECTS of man and opt courses should >= 45
****)
let isValidCourseGroup (man,opt) cb =
    disjoint man opt && 
    sumECTS man cb <= 45 && 
    sumECTS man cb + sumECTS opt cb >= 45;;


type BasicNaturalScience = CourseGroup
type TechnologicalCore = CourseGroup
type ProjectProfessionalSkill = CourseGroup
type Elective = CourseNo -> bool
type FlagModel = BasicNaturalScience * TechnologicalCore * ProjectProfessionalSkill * Elective
type CoursePlan = Set<CourseNo>

(**** 6. isValid: FlagModel -> CourseBase -> bool
            test whether a flag model is valid:
            1. the three course groups bns, tc and pps are all valid.
            2. no course belongs to more than one of the course groups bns, tc and pps.
            3. any course belong to a course group bns, tc or pps must qualify as an elective course, that is it must satisfy the predicate ep
****)
let pAllValidP xs cb = 
    pForAll (fun x -> 
        isValidCourseGroup x cb) xs;;

let pDisjointWithRestP cg cgs = 
    pForAll (fun x ->
        disjoint cg x) cgs;;

let rec pDisjointedCGs cgs =
    match cgs with
    | [] -> true
    | x::xt -> pDisjointWithRestP x xt && pDisjointedCGs xt;;

pDisjointedCGs [set [1];set [2];set [3]];;


let isValid ((bnsom,bnso),(tcm,tco),(ppsm,ppso),ep) cb = 
    let cgs = [(bnsom,bnso);(tcm,tco);(ppsm,ppso)]
    let cnss = [bnsom;bnso;tcm;tco;ppsm;ppso]
    pAllValidP cgs cb &&
    pDisjointedCGs cnss &&
    pForAll (fun x ->
        let cns = Set.toList x
        pForAll ep cns) cnss;;         //or pForAll (fun cn -> ep cn) cns instead of pForAll ep cns
              


(**** 7.

****)
let checkPlan cs (bns,tc,pps,ep) cb = 
    isValid (bns,tc,pps,ep) cb && 
    sumECTS cs cb = 180 &&
    pForAll ep (Set.toList cs);;
    



  
    
    



