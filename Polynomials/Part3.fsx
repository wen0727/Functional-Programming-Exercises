(* Part3: Preserving an invariant *)
(* isLegal *)
#load "Part1.fsx"
#load "Part2.fsx"
open Part1
open Part2
#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
#r @"FsCheck.dll"
open FsCheck
let addInv (p1:int list) (p2:int list) = isLegal(prune(add p1 p2))
prune(add [-2] [0; 1; 0])
let testAddProp = Check.Quick addInv
