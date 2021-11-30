(* Part 4: Tagged values - Degrees of polynomials *)
(** Declare a type Degree, we construct MinusInf to represent the degree of a 0;
    and for non zero polynpomial we use Fin of int to represent the degree of the polynomial;
**)
type Degree = MinusInf
            | Fin of int
(** Declare a function for counting the degrees of polynormials.
        degree: Poly -> Degree
**)
let rec p2Deg = function
                | [] -> 0
                | _::pt -> 1 + (p2Deg pt);;
              
let degree ps = 
    match ps with
    | [] -> MinusInf
    | _::pt -> Fin (p2Deg pt);;
degree [];;
degree [5];;
degree [2;0;0;3];;
degree [1;2;3;0;0;0]

(** Test the built-in "<=" operator betweeb the type constructors of type Degree **)
MinusInf <= Fin 0
Fin 3 <= Fin 4 

(** Declare an F# function 
    addD: Degree -> Degree -> Degree adding degrees
        addition of finite degrees would be represent as addition of the deegrees for instance Fin 7 + Fin 8 = Fin 15;
        addition any degrees with the minus inifinity would be minus infinity.

(** Other method ? **)
let addM dp dq = 
    match (dp,dq) with
    | (Fin N, Fin M) -> Fin (N+M)
    | _ -> MinusInf
let addD dp dq = 
    match (dp,dq) with
    | (MinusInf,_) | (_,MinusInf) -> MinusInf
    | _ -> addM dp dq

**)
let addD dp dq = 
    match (dp,dq) with
    | (MinusInf,_) | (_,MinusInf) -> MinusInf
    | (Fin N,Fin M) -> Fin (N+M);;
addD (Fin 7) (Fin 8)

(** Declare multC with higher-order functions from the List library. multC's output should be equal to mulC. **)
let multC c p = 
    if c=0 
    then []
    else List.map (fun X -> c*X) p

#load "Part1.fsx"
open Part1
#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"
open FsCheck

let multCVmulC c p = multC c p = mulC c p
let testmultCVmulC = Check.Quick multCVmulC

