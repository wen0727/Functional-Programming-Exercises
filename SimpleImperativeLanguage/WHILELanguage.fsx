(* Based on a natural semantics of WHILE *)
(* Arithmetical expressions, abstract syntax - parse trees *) 
type AExp =                           
          | N  of int                 (* numbers                  *)
          | V  of string              (* variables                *)
          | Add of AExp * AExp        (* addition                 *)
          | Mul of AExp * AExp        (* multiplication           *)
          | Sub of AExp * AExp;;      (* subtraction              *)


type BExp =                          (* boolean expressions      *)
          | TT                       (* true                     *)
          | FF                       (* false                    *)
          | Eq of AExp * AExp        (* equality                 *)
          | Lt of AExp * AExp        (* less than                *)
          | Neg of BExp              (* negation                 *)
          | Con of BExp * BExp;;     (* conjunction              *)

type Stm  =                            (* statements             *)
          | Ass of string * AExp       (* assignment             *)
          | Skip                       (* next statement *)
          | Seq of Stm * Stm           (* sequential composition *)
          | ITE of BExp * Stm * Stm    (* if-then-else           *)
          | While of BExp * Stm        (* while                  *)         
          | IfThen of BExp * Stm
          | RepeatUntill of BExp * Stm
          | Inc of string;;

(* Place holder *)
type State = Map<string,int>;;

(* update: string -> int -> State -> State  *)
let update x v s = Map.add x v s;; 

(* Semantics *)
(* A: AExp -> State -> int                  *)
let rec A a s      = 
   match a with 
    | N n         -> n
    | V x         -> Map.find x s
    | Add(a1, a2) -> A a1 s + A a2 s
    | Mul(a1, a2) -> A a1 s * A a2 s
    | Sub(a1, a2) -> A a1 s - A a2 s;; 

(* B: BExp -> State -> bool                  *)
let rec B b s =
   match b with 
   | TT          -> true
   | FF          -> false
   | Eq(a1,a2)   -> A a1 s  = A a2 s
   | Lt(a1,a2)   -> A a1 s < A a2 s 
   | Neg b       -> not (B b s)
   | Con(b1,b2)  -> B b1 s && B b2 s;;
(* Update place holder, WHILE language interpreter - compiler *)
(* I: Stm -> State -> State                          *)
let rec I stm s =
    match stm with 
    | Ass(x,a)         -> update x (A a s) s
    | Skip             -> s
    | Seq(stm1, stm2)  -> let ns = I stm1 s
                          I stm2 ns
    | ITE(b,stm1,stm2) -> if B b s
                          then I stm1 s 
                          else I stm2 s
    | While(b,stm1)    -> if B b s
                          then let ns = I stm1 s 
                               I stm ns
                          else s
    | IfThen(b,stm1)   -> if B b s 
                          then I stm1 s
                          else s
    | RepeatUntill(b,stm1) -> if B b s 
                              then let ns = I stm1 s
                                   I (stm) ns
                              else s
    | Inc x -> update x (Map.find x s + 1) s;;


(* Factorial computation 
{pre: x = K and x>=0} 
   y:=1 ; while !(x=0) do (y:= y*x;x:=x-1) 
post: {y = K!}
*)

let fac = Seq(Ass("y", N 1), 
              While(Neg(Eq(V "x", N 0)), 
                    Seq(Ass("y", Mul(V "x", V "y")) , Ass("x", Sub(V "x", N 1)) ))
             );;




(* Define an initial state                           *)
let s0 = Map.ofList [("x",4)];;

(* Interpret the program                             *)
let s1 = I fac s0;;

let e1 = I (Inc "y") s1;;
(* Inspect the resulting state                       *)
Map.find "y" e1;;