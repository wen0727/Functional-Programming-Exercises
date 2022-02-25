(* Part3: Preserving an invariant *)
(* isLegal *)
#load "Part1.fsx"
#load "Part2.fsx"
open Part1
open Part2
#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"
open FsCheck
let addInv p1 p2 = isLegal(add (prune p1) (prune p2));;
let addInvP3 p1 p2 = isLegal(prune(add p1 p2));;
prune(add [-2] [0; 1; 0])
let _ = Check.Quick addInvP3
let _ = Check.Quick addInv


let add p1 p2 = prune (add p1 p2);;
let mulC n p = prune (mulC n p);;
let sub p1 p2 = prune (sub p1 p2);;
let mulX p = prune (mulX p);;
let mul p1 p2 = prune (mul p1 p2);;
let derivative p = prune (derivative p);;
let compose p1 p2 = prune (compose p1 p2);;



