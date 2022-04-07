(* Simple Lambda Caculus Interpreter *)

(* Part 1 Impure lambda with constants *)
type Lambda =  | L of string * Lambda
               | A of Lambda * Lambda
               | V of string
               | O of string
               | I of int 
               | B of bool;; 

// free: Lambda -> Set<string> 
(* e.g.
For abstraction, 
    L("x",M),  "x" is bound, it should be removed from the FV set. 
For application
    L1 = A(M1,M2) fv(L1) = union(fv(M1,M2))
For variable 
    x != in FV
Scope:
    A(L("x",A(L("x",V "x"),V "x")),I 1) has different scope, 
        so the inner V "X" has to be renamed.
*)
let rec fFree acc =
    function 
    | L(s,_)                    -> Set.remove s acc
    | A(t1,t2)                  -> let tl = fFree acc t1
                                   let tr = fFree acc t2
                                   Set.union tl tr
    | V x                       when not(Set.contains x acc) -> Set.add x acc
    | _                         -> acc;;
let free t = fFree (Set.empty) t;;


// nextVar: string -> string --- generates a fresh variable                 
let nextVar = let n   = ref 0
              let f x = let xnew = x+"#"+string n.Value
                        n.Value <- 1 + n.Value
                        xnew
              f;;         

// subst: Lambda -> string -> Lambda -> Lambda  --- sustitution that takes case of clashes
(* e.g. substitution
For abstraction,
    when the names clash, rename the abstraction and rename the sub terms and redo the substitution with the new terms
    when the names doesn't clash, just substitute to the sub terms
For the application, 
    just substitute the left and right subterms.
For the variale, 
    when the names clash, just replace the variable with new term
otherwise just bind to original value.
*)
(* e.g. alpha renaming
For abstraction, 
    when the names clash, renaming it with new one and the subterms
For applications
    rename left and right subterms
For variables
    when the names clash, just replace it with new name
other pattern, would just bind with original value.
*)

let rec subst t x ta = 
    match t with
    | L(s,t1)  -> if s=x 
                  then let nx = nextVar x
                       subst (L(nx, alpha s nx t1)) x ta
                  else L(s, (subst t1 x ta))
    | A(t1,t2)  -> A((subst t1 x ta),(subst t2 x ta))
    | V x1      when x1=x -> ta 
    | _         -> t
and alpha x nx t = 
    match t with
    | L(s,t1)   -> if s=x
                   then L(nx, alpha s nx t1) 
                   else L(s, alpha x nx t1) 
    | A(t1,t2)  -> A(alpha x nx t1,alpha x nx t2)
    | V x1      when x1=x -> V nx
    | _ -> t;;

//test for name collision
alpha "x" "x#0" (L("x",L("x",A(V "x", V "x"))));;
alpha "x" "x#0" (A(A(A(O "ite",A(A(O "=",V "x"),I 0)),V "x"),V "x"));;
subst (L("x",L("x",L("x",A(V "x", V "x"))))) "x" (I 4);;
subst (A(A(A(O "ite",A(A(O "=",V "x"),I 0)),V "x"),V "x")) "x" (I 4);;

// red: Lambda -> Lambda option  --- reduces the outermost, leftmost redex, is such redex exists.
// Makes at most one reduction
(* 
    The function converts lambda beta redex to head normal form,
        if no more beta redex at head position, then start to convert right terms 
*)
let rec red t = match t with 
                | A(L(x,t1),t2)                   -> Some(subst t1 x t2)
                | A(A(O "=", I a), I b)           -> Some(B(a=b))
                | A(A(O "+", I a), I b)           -> Some(I(a+b))
                | A(A(O "-", I a), I b)           -> Some(I(a-b))
                | A(A(O "*", I a), I b)           -> Some(I(a*b))
                //| A(A((O _) as op, ((I _) as i1)), t2)     -> Some(A(A(op, i1), Option.get (red t2)))
                //| A(A((O _) as op, t1), t2)                -> Some(A(A(op, Option.get (red t1)), t2))
                | A(A(A(O "ite", B true),t1),t2)  -> Some t1
                | A(A(A(O "ite", B false),t1),t2) -> Some t2
                //| A(A(A(O "ite", b),t1),t2)       -> Some (A(A(A(O "ite", Option.get (red b)),t1),t2))
                | L(x,t1)                         -> match red t1 with
                                                     | Some l   -> Some(L(x,l))           
                                                     | None     -> None
                | A(t1,t2)                        -> match red t1 with  // Some (A(Option.get (red t1),t2))
                                                     | Some l   -> Some(A(l,t2))
                                                     | None     -> match red t2 with 
                                                                   | None   -> None 
                                                                   | Some l -> Some(A(t1,l))
                | _                               -> None;; 

// reduce: Lambda -> Lambda  --- normal-order reduction of a term                  
(* The function recursively apply head reduction until normal form is achieved. 
*)

let rec reduce t = 
    match red t with
    | None      -> t
    | Some l     -> reduce l;;

//reduce (A (A (A (O "ite", A (A (O "=", I 4), I 0)), I 4), I 4))

// Examples  
let t1 = L("x",L("y", A(A(O "+", V "x"), V "y")));;

let t2 = A(t1, I 3);;

let t3 = A(t2, I 4);;

let v3:Lambda = reduce t3;;

// Turings fixed-point combinator
(* the combinator can be formed as the formular showed in wiki *)
let Y = let t = L("x",L("y",A(V "y", A(A(V "x", V "x"), V "y"))))
        A(t,t);;

// Functional for the factorial function 
let nEqual0 = A(A(O "=", V "n"),I 0);;
let nMinus1 = A(A(O "-", V "n"), I 1);;
let nNext = A(V "f", nMinus1);;
let nMul = A(A(O "*",V "n"),nNext);;
let F:Lambda =
    L("f",L("n",A(A(A(O "ite", nEqual0),I 1),nMul)));;

let fact = A(Y,F);;

// Examples
let fac4 = A(fact,I 4);;
(* Tests 
let fac1 = A(fact,I 1);;
// Y combinator
let reg1 = red fac1;;
let reg2 = red (Option.get (reg1));;
let reg3 = red (Option.get (reg2));;
let reg4 = red (Option.get (reg3));;
let reg5 = red (Option.get (reg4));;
let reg6 = red (Option.get (reg5));;
let reg7 = red (Option.get (reg6));;
let reg8 = red (Option.get (reg7));;
let reg9 = red (Option.get (reg8));;
let reg10 = red (Option.get (reg9));;
let reg11 = red (Option.get (reg10));;
let reg12 = red (Option.get (reg11));;
let reg13 = red (Option.get (reg12));;
let reg14 = red (Option.get (reg13));;
*)

// 
let vfac4:Lambda = reduce fac4;;

let fac8 = A(fact,I 8);;

let vfac8:Lambda = reduce fac8;;

(* Part2 Pure Lambda*)

(* church numerals *)

// convenient shorthands
let f = V "f"
let g = V "g"
let h = V "h"
let x = V "x"
let y = V "y" 
let u = V "u" 
let v = V "v"    
let m = V "m"
let n = V "n"
let p = V "p"
    
let zero = L("f", L("x", x));;
let one  = L("f", L("x", A(f,x)));;
let two  = L("f", L("x", A(f, A(f, x))));;

//let succ = L("n", L("f", L("x", A(A(n, f),A(f, x)))));;
let succ = L("n", L("f", L("x", A(f,A(A(n,f),x)))));;
//let add = L("m", L("n", L("f",L("x",A(A(m, f), A(A(n, f), x))))));;
let add = L("m", L("n", L("f",L("x",A(A(m, f), A(A(n, f), x))))));;
let pred = L("n", L("f", L("x",A(A(A(n, L("g",L("h", A(h, A(g,f))))),L("u",x)),L("u",u)))));; 

// toInt: Lambda -> int   --- converts a Church numeral to an integer
(*
let rec toInt t =
    match reduce t with
    | L(s1,L(s2,app))   -> fCountL 0 s1 s2 (reduce app)
    | _                 -> failwith "Given Lambda term is not a church numeral."
and fCountL acc s1 s2 =
    function
    | V x2          when x2=s2 -> acc
    | A(V x1,V x2)  when x1=s1 && x2=s2 -> acc+1
    | A(V x1,t2)    when x1=s1 -> fCountL (acc+1) s1 s2 t2
    | A(t1,t2)  ->  let tl = fCountL acc s1 s2 t1
                    fCountL tl s1 s2 t2 
    | _         ->  failwith "Given Lambda term is not a church numeral.";;
*)

let rec toInt t =
    match reduce t with
    | L(s1,L(s2,app))   -> fCountL 0 s1 s2 (reduce app)
    | _                 -> failwith "Given Lambda term is not a church numeral."
and fCountL acc n1 n2 l =
    match l with
    | V x2          when x2=n2 -> acc
    | A(V x1,t2)    when x1=n1 -> fCountL (acc+1) n1 n2 t2
    | A(t1,t2)  ->  let tl = fCountL acc n1 n2 t1
                    fCountL tl n1 n2 t2 
    | _         ->  failwith "Given Lambda term is not a church numeral."

// Test of toInt
toInt two;;
// Test of succ, add, pred and mult
let egSucc1 = A(succ,one);;
let egSucc2 = (A(A(add,A(succ,one)),two));;
(*
let egSucc2 = (A(A(add,A(succ,one)),two));;
let eg1Succ2 = red (egSucc2);;
let eg2Succ2 = red (Option.get eg1Succ2);;
let eg3Succ2 = red (Option.get eg2Succ2);;
let eg4Succ2 = red (Option.get eg3Succ2);;
let eg5Succ2 = red (Option.get eg4Succ2);;
let eg6Succ2 = red (Option.get eg5Succ2);;
let eg7Succ2 = red (Option.get eg6Succ2);;
let eg8Succ2 = red (Option.get eg7Succ2);;
let eg9Succ2 = red (Option.get eg8Succ2);;
let eg10Succ2 = red (Option.get eg9Succ2);;
*)

reduce egSucc2;;
toInt egSucc2;;

// mult: Lambda    --- multiplication of Church numerals

let mult:Lambda = L("m",L("n",L("f",L("x",A(A(m,A(n,f)),x)))));;
// Test of mult
toInt (A(A(mult,two),two));;

// Church Booleans

let True  = L("x", L("y", x));;
let False = L("x", L("y", y));;
let ITE   = L("p",L("x",L("y",A(A(p,x),y))));;

let rec toBool t =
    match reduce t with
    | L(s1,L(s2,app)) -> toPredicate s1 s2 (reduce app)
    | _               -> failwith "The Lambda term is not church boolean."
and toPredicate s1 s2 =
    function
    | V x   when x=s1 -> true
    | V y   when y=s2 -> false
    | _               -> failwith "The Lambda term is not church boolean.";;

// Test of ITE

// Test of IsZero with applying church numeral zero
let IsZero = L("n",A(A(n,L("x",False)),True));;
toBool (A(IsZero,zero));;
// Test IsZero with applying variable, fase when the variable > 0
toBool (A(IsZero,two));;

reduce (A(A(A(ITE,A(IsZero,two)),one),two));;
//if NN=0 then 1 else NN
(A(A(A(A(ITE,L("NN",A(IsZero,V "NN"))),one),zero),two))
red (A(A(A(A(ITE,L("NN",A(IsZero,V "NN"))),one),zero),two))
reduce (A(A(A(A(ITE,L("NN",A(IsZero,V "NN"))),one),zero),two));;
toInt (A(A(A(A(ITE,L("NN",A(IsZero,V "NN"))),one),zero),two));;

// Make en new declaration for F -- the functional for the factorial function 
let fName = V "f";;
let vName = V "n";;
let pN0     = A(IsZero,vName);;
let nPred   = A(pred,vName);;
let fNPred  = A(fName,nPred);;
let nTimes  = A(A(mult,vName),fNPred);;
//f.n. if n=0 then 1 else n*f(n-1)
let F' =
    L("f",L("n",A(A(A(ITE, pN0),one),nTimes)));;


let factNew = A(Y, F');;

// Test of factorials

let vfact4:Lambda = reduce (A(factNew, A(A(add,A(succ, one)),two)));;
toInt vfact4;;

let vfact1:Lambda = reduce (A(factNew,one));;
toInt vfact1;;

let vfact2:Lambda = reduce (A(factNew,two));;
toInt vfact2;;
// Try to compute 5! and be a little patient
let vfact5:Lambda = reduce (A(factNew,A(A(add,A(succ, two)),two)));;
toInt vfact5;;
