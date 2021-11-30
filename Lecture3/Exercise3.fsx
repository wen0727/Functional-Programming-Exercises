(* The relative path *)
#load "..\Lecture1\Exercise1.fsx"
#load "..\Lecture2\Exercise2.fsx"
(* Specifies an assembly search path in quotation marks. *)
#I @"C:\Users\wenha\.nuget\packages\fscheck\2.16.3\lib\net452"
(* References an assembly on disk *)
#r @"FsCheck.dll"
(* To omit typeing Exercise."Function" *)
open Exercise2 
open Exercise1
open FsCheck
(* Exercise 3 *)
(** HR 4.16 
written exercise on note. 09/22
Consider the declaration:

let rec f g = function
    | [] -> []
    | x::xs -> g x :: f (fun y -> g(g y)) xs;;

Find the type for f and explain the value of the expression:

    f g [x_0;x_1;x_2;...;x_(n-1)]

Solution:
    Assume x: Alpha then xs: Alpha list.
    g(x) and g(g(y)) should have the same type.
        x and g(y) should have the same type which implies g(y): Alpha
        Thus (g x :: f (fun y -> g(g y)) xs): Alpha list
    f g [x_0;x_1;x_2;...;x_(n-1)] = 
        [g(x_0);g(g(x_1));...;g^(n-1)(x_n-1)]   
**)

(** Simple Company Club **)
(*** 1.
Types for the important concetps of the problem formulation including, at least, types 
for the register, themes of interests, descriptions and arrangement.
***)
(**** Basic type, they can be omitted ****)
type Name = string
type Phnumber = string
type Byear = int
type Theme = string
(**** Important types ****)
type Themes = Theme list
type Description = Phnumber*Byear*Themes
type Register = (Name*Description) list
type Arrangement = bool

(*** 2. 
A declaration of a register reg, a declaration of an arrangement p_1 for the above 
described arrangement p_1, and a declaration of an arrangement p_2 that is directed to 
young club members that are interested in either "soccer" or "jazz" or both. These 
declarations should be constructed so that they can serve as illustrative examples.
***)
let rec includeThs s = function
    | [] -> false 
    | X::tt -> s=X || includeThs s tt

let p1 (_,yb,ths) = yb > 1982 && includeThs "soccer" ths && includeThs "jazz" ths
let p2 (_,yb,ths) = yb > 1982 && includeThs "soccer" ths || includeThs "jazz" ths
(*** 3. 
A declaration of a function extractTargetGroup p r that gives a list with names and 
phone numbers of the members in register r that may be interested in the arrangement 
p. State the type of extractTargetGroup in a comment. Make use of the type names 
introduced under point 1. above, so that the type reflects the intention with the function.  

extractTargetGroup: bool -> Name*Description list -> Name*Phnumber list

(* Use "as" for forming recipie *)
let rec extractTargetGroup p r = 
    match r with 
    | [] -> []
    | (n,((no,_,_) as desc))::rt -> let NPS = extractTargetGroup p rt
                                    if p(desc)
                                    then (n,no)::NPS
                                    else NPS;;
(* No tail-recursive *)
let rec extractTargetGroup p r = 
    match r with 
    | [] -> []
    | (n,(no,yb,ths))::rt -> let NPS = extractTargetGroup p rt
                             if p (no,yb,ths)
                             then (n,no)::NPS
                             else NPS;;

***)

(**** Declare of a register reg: Cregrigster ****)
let reg = [("Wen",("123456",1987,["soccer";"jazz"]));
           ("Helen",("123456",1980,["soccer";"jazz"]));
           ("Lina",("123456",1990,["soccer"]));
           ("Jack",("123456",1977,["jazz"]));
           ("Rose",("123456",1983,["tennis";"basketball";"soccer"]));
           ("Aiden",("123456",1983,["soccer";"basketball";"swim"]))]

let rec findNameAndNum p CT = function
    | [] -> List.rev CT (*If order doesn't matter then just CT*)
    | (X,(Y,Z,TS))::rt -> if p(Y,Z,TS)
                          then findNameAndNum p ((X,Y)::CT) rt
                          else findNameAndNum p CT rt;;
let extractTargetGroup p r = findNameAndNum p [] r

(*** 4. 
Tests of extractTargetGroup involving reg, p_1 and p_2
***)
extractTargetGroup p1 reg;;
extractTargetGroup p2 reg;;

(** Exercise: Merge-sort and property-based testing **)
(*** merge : A list -> A list -> A list
    merge [1;4;9;12] [2;3;4;5;10;13] = [1;2;3;4;4;5;9;10;12;13]

Invariant: 
    input lists should be ordered 
Assumption for function merge xs ys:
    xs and ys are ordered lists.
***)
let rec merge xs ys =
    match (xs,ys) with
    | ([], _) -> ys
    | (_, []) -> xs
    | (X::xt, Y::yt) -> if X<=Y 
                        then X::merge xt ys
                        else Y::merge xs yt;;

(*** split: A list -> A list*A list 
The function was last exercise from lecture, can be loaded and reuse, here we would like to show some tests.
***)
split [1;2;3;4;5];;

(*** sort: A list -> A list 
We can recursively apply split * merge functions to the input list. Empty list and singleton list would be trivial bind to itself trivially.
***)
let rec sort xs =
    match xs with
    | [] -> []
    | [X] -> [X]
    | _ -> let (YS,ZS) = split xs
           merge (sort YS) (sort ZS);;

sort [7;4;1;2;0;6;7;5;3];;

(*** Correctness 
The output of sort should satisfy ascending order.
    ordered: int list -> bool
We should define a predicate to test whether a list is an ordered list.
The correctness property can be expressed by the predicate as follows:
    let orderedSort(xs: int list) = ordered(sort xs)
***)
let rec lowestNum s = function
    | [] -> true
    | X::tt -> s<=X && lowestNum s tt;;

let rec ordered xs =
    match xs with
    | [] -> true
    | X::xt -> lowestNum X xt && ordered xt;;

let orderedSort(xs: int list) = ordered(sort xs);;
(*** Property-based testing by using FsCheck ***)
let commProp(x,y) = x+y = y+x;;
let commPropTest = Check.Quick commProp;;
let commPropTestVerbose = Check.Verbose commProp;;

(*** Test the property orderedSort using FsCheck 
It is important for FsCheck that the predicates being tested are not polymorphic types.
***)
let orderedSortTest = Check.Quick orderedSort;;
let orderedSortTestVB = Check.Verbose orderedSort;;

(*** Further property-based testing 
The main goal of property-based test is for program correctness rather than making test cases.

Now, we should address second property of a sorting function. To count elements' occurencies in a list.
For example, the counting for [3;2;6;3;2;1] is [(1;1);(2;2);(3;2);(6;1)].
***)

(**** 1. increment(x,cnt) the value of increment(i,cnt) is the counting obtained from cnt by adding 1. ****)
let increment(x,cnt) = (x,cnt+1)

(**** 2. toCounting xs to count element occurencies of a list ****)
let rec editOcc s ts =
    match ts with
    | [] -> []
    | (X,occ)::tt -> if s=X 
                     then increment(X,occ)::tt
                     else (X,occ)::editOcc s tt
    

let rec toCounting xs = 
    match xs with
    | [] -> []
    | X::xt -> let EOS = toCounting xt
               if (memberOf X xt)=false
               then insert (increment(X,0),EOS)
               else editOcc X EOS

(**** 3. Test the property: ordered(toCounting xs) ****)
let orderedEOS (xs: int list) = ordered(toCounting xs)
let _ = Check.Quick orderedEOS

(**** 4. Test the property toCounting xs = toCouting(sort xs) ****)
let orderedEOSCorrect (xs: int list) = toCounting xs = toCounting (sort xs)
let _ = Check.Quick orderedEOSCorrect