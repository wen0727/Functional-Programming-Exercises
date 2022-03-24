(* Simple compiler *)
(* Part 1: Simple stack machine *)
(* Model of instruction set *)
type Instruction = | ADD | SUB | SIGN | ABS | PUSH of int
(* Execution of an instruction maps a stack to new stack: 
    ADD stack [a b c] yields a new staks [(b+a) c]
    SIGN stack [a b] yields [-a b]
    ABS STACK [a] [-a]
    PUSH r with the stack [a b c] yields [r a b c]
*)

(* Model the stack and declare a function to interpret the execution of a single instruction 
    type Stack
        the stack for the machine is modeled with list of integers regarding to the instuction set.
    intpInstr: Stack -> Instruction -> Stack
*)

type Stack = int list
(* Simple instruction set for calculating value expression, no branching, function calls and memory managemtn. *)
let rec intpInstr stk ins = 
    match ins with
    | ADD -> match stk with
             | o1::o2::ot -> intpInstr ot (PUSH (o2+o1))
             | _ -> stk
    | SUB -> match stk with
             | o1::o2::ot -> intpInstr ot (PUSH (o2-o1))
             | _ -> stk
    | SIGN -> match stk with
              | o::ot -> intpInstr ot (PUSH (0-o))
              | _ -> stk
    | ABS -> match stk with
             | o::ot -> if o>=0 then intpInstr ot (PUSH o)
                        else intpInstr ot (PUSH -o)
             | _ -> stk
    | PUSH i -> i::stk

(* Declare a function to interpret the execution of a program: 
    exec: Instruction list -> int
*)
let rec exec stk =
    function
    | [] -> match stk with
            | i::_ -> i
            | [] -> 0
    | ins::inst -> exec (intpInstr stk ins) inst;;

(* Part 2 Expressions: Syntax and semantics *)
(* Model of expression Exp which are 
    variable constructor X
    integer constant constructor C
    operator constructor Add
                         Sub
                         Minus
                         Abs
*)
(* The type declaration defines abstract syntax for the expression. 
    The value of the type concrete examples.
*)
type Exp = X 
         | C of int
         | Add of Exp*Exp
         | Sub of Exp*Exp
         | Minus of Exp
         | Abs of Exp
(* Sematics of the expression. *)
let rec sem e x =
    match e with 
    | X -> x
    | C n -> n
    | Add (e1,e2) -> sem e1 x + sem e2 x
    | Sub (e1,e2) -> sem e1 x - sem e2 x
    | Minus e -> -(sem e x)
    | Abs e -> let v = sem e x
               if v>=0 then v
               else -v

(* Part 3: Compilation to stack-machine code 
    The model of the compiler should construct executable instruction list.
    compile: Exp -> int -> Instruction list
*)
let rec fCompile e x insl =
    match e with
    | X -> (PUSH x)::insl
    | C n -> (PUSH n)::insl
    | Add (e1,e2) -> let tr = fCompile e2 x (ADD::insl)
                     fCompile e1 x tr
    | Sub (e1,e2) -> let tr = fCompile e2 x (SUB::insl)
                     fCompile e1 x tr
    | Minus e -> fCompile e x (SIGN ::insl)
    | Abs e -> fCompile e x (ABS::insl)
let compile e x = fCompile e x [];;

#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"
open FsCheck
(* Correctness of compile 
    Compare correctness of compiled expression regarding to the semantics
*)
(* Quick test *)
let pCorrectCompile e x = exec [] (compile e x) = sem e x;;
let _ = Check.Quick pCorrectCompile;;
let _ = Check.Verbose pCorrectCompile;;
(* Controlled test *)
let pCCorrectCompile s n r = 
    let genExp = FsCheck.Arb.generate<Exp>
    let varX = Gen.choose(-r,r) |> Gen.sample 0 1
    let exps = Gen.sample s n genExp
    let prop e x =
        exec [] (compile e x) = sem e x
    (exps, List.forall (fun e -> 
                List.forall (prop e) varX) exps);; 
        
pCCorrectCompile 100 100 100;;

(* Part 4: Optimization, Expression reductions 
    red: Exp -> Exp
    Add(C i; C j) is reduced to C(i + j)
    Add(e; C 0) is reduced to e
    Add(C 0; e) is reduced to e

    Sub(C i; C j) is reduced to C(i - j)
    Sub(e; C 0) is reduced to e
    Sub(C 0; e) is reduced to Minus e

    Minus(C i) is reduced to C(-i)
    Minus(Minus e) is reduced to e

    Abs(C i) is reduced to C(abs(i))
    Abs(Minus e) is reduced to Abs e
    Abs(Abs e) is reduced to Abs e
*)
let rec red exp =
    match exp with
    | X -> X
    | C n -> C n
    | Add (e1,e2) -> match (e1,e2) with
                     | (C n1, C n2) -> C (n1+n2)
                     | (e1, C 0) -> red e1
                     | (C 0, e2) -> red e2
                     | _ -> Add (red e1,red e2)
    | Sub (e1,e2) -> match (e1,e2) with
                     | (C n1, C n2) -> C (n1-n2)
                     | (e1, C 0) -> red e1
                     | (C 0, e2) -> red (Minus e2)
                     | _ -> Sub (red e1,red e2)
    | Minus e -> match e with
                 | C n -> C (-n)
                 | Minus e1 -> red e1
                 | _ -> Minus (red e)
    | Abs e -> match e with
               | C n -> if n>=0 then C n
                        else C -n
               | Minus e1 -> red (Abs e1)
               | Abs e1 -> red (Abs e1)
               | _ -> Abs (red e);;

let pCorrectRed e x = sem e x = sem (red e) x;;
let _ = Check.Quick pCorrectRed;;
let _ = Check.Verbose pCorrectRed;;

(* Declare a function reducible: Exp -> bool 
    Atom is not reducible.
*)
let rec reducible exp =
    match exp with
    | X -> false
    | C _ -> false
    | Add (e1,e2) -> reducible e1 && reducible e2
    | Sub (e1,e2) -> reducible e1 && reducible e2
    | Minus e -> reducible e
    | Abs e -> reducible e;;

let pCorrectReducible e = not (reducible (red e));;
let _ = Check.Quick pCorrectReducible;;
let _ = Check.Verbose pCorrectReducible;;

