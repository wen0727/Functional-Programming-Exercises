(* Interpreter for a simple WHILE-language.                          *)
(* Program skeleton                                                  *)
(* Based on a natural semantics of WHILE                             *)

type AExp =                           (* Arithmetical expressions *) 
          | N  of int                 (* numbers                  *)
          | V  of string              (* variables                *)
          | Add of AExp * AExp        (* addition                 *)
          | Mul of AExp * AExp        (* multiplication           *)
          | Sub of AExp * AExp;;        (* subtraction              *)
          


type BExp =                          (* boolean expressions      *)
          | TT                       (* true                     *)
          | FF                       (* false                    *)
          | Eq of AExp * AExp        (* equality                 *)
          | Lt of AExp * AExp        (* less than                *)
          | Neg of BExp              (* negation                 *)
          | Con of BExp * BExp;;     (* conjunction              *)

type Stm  =                            (* statements             *)
          | Ass of string * AExp       (* assignment             *)
          | Skip
          | Seq  of Stm * Stm          (* sequential composition *)
          | ITE   of BExp * Stm * Stm  (* if-then-else           *)
          | While of BExp * Stm        (* while                  *)
          | IfThen of BExp * Stm
          | RepeatUntill of BExp * Stm;;



type State = Map<string,int>;;
type M<'a> = State -> 'a*State;;

// ret: 'a -> M<'a>
let ret v = fun s -> (v,s);;

// bind: M<'a> -> ('a -> M<'b>) -> M<'b>
let bind comp f = (fun s -> let (a,s') = comp s 
                            f a s');;

let (>>=) x f = bind x f;;

//get: string -> M<int>
let get x = fun s -> (Map.find x s,s)

//put: string -> int -> M<unit>
let put x v = fun s -> ((),Map.add x v s)

(* A: AExp -> M<int>                   *)
let rec A a       = 
   match a with 
    | N n         -> ret n
    | V x         -> get x 
    | Add(a1, a2) -> A a1 >>= fun v1 -> A a2 >>= fun v2 -> ret (v1+v2)
    | Mul(a1, a2) -> A a1 >>= fun v1 -> A a2 >>= fun v2 -> ret (v1*v2)
    | Sub(a1, a2) -> A a1 >>= fun v1 -> A a2 >>= fun v2 -> ret (v1-v2)

(* B: BExp -> M<bool>                  *)
let rec B b      =
   match b with 
   | TT          -> ret true
   | FF          -> ret false
   | Eq(a1,a2)   -> A a1 >>= fun v1 -> A a2 >>= fun v2 -> ret (v1=v2)
   | Lt(a1,a2)   -> A a1 >>= fun v1 -> A a2 >>= fun v2 -> ret (v1<v2)
   | Neg b       -> B b >>= fun p -> ret (not p)
   | Con(b1,b2)  -> B b1 >>= fun p1 -> B b2 >>= fun p2 -> ret (p1&&p2);;

(* I: Stm -> M<unit>                          *)
let rec I stm          =
    match stm with 
    | Ass(x,a)             -> A a >>= fun v -> put x v
    | Skip                 -> ret ()
    | Seq(stm1, stm2)      -> I stm1 >>= fun () -> I stm2 
    | ITE(b,stm1,stm2)     -> B b >>= function
                                      | true  -> I stm1
                                      | false -> I stm2
    | While(b,stm1)        -> B b >>= function
                                      | true  -> I stm1 >>= fun () -> I stm
                                      | false -> ret ()
    | IfThen(b,stm1)       -> B b >>= function
                                      | true  -> I stm1 
                                      | false -> ret ()
    | RepeatUntill(b,stm1) -> B b >>= function
                                      | true  -> I stm1 >>= fun () -> I stm
                                      | false -> ret ();;


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
let ((),s1) = I fac s0;;

(* Inspect the resulting state                       *)
Map.find "y" s1;;


