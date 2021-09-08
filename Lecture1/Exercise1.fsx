(* After lecture 1 *)
(** Blackboard exercise **)
(*** memberOf x ys is true iff x occurs in the ys list ***)
let rec memberOf x ys =
    match ys with 
    | [] -> true
    | y::yt -> x=y || memberOf x yt;;

memberOf 'x' ['y';'z'];;
(*** insert(x,ys) is ordered list obtained by inserting the x to the ordered list ys ***)
let rec insert(x,ys) =
    match ys with
    | [] -> [x]
    | y::yt when x<=y -> x::y::yt
    | y::yt -> y::insert(x,yt);;

insert(1,[0;2;3;4]);;
(*** sort(xs) gives an ordered version of xs ***)
let rec sort(xs) =
    match xs with
    | [] -> []
    | x::xt -> insert(x,sort(xt));;

sort([1;2;3;4;0]);;

(** Exercise 1 **)
(*** 1.4
Declare a recursive function f:int -> int, where 
    f(n)=1+2+...+(n-1)+n 
for n>=0. (Hint: use two clauses with 0 and n as patterns.) 
Give an evaluation for f(4).
***)
let rec f1_4(n) =
    match n with
    | 0 -> 0
    | n when n>0 -> n + f1_4(n-1)
    | _ -> failwith "n should be larger or equal than 0.";;
f1_4(4);;

(*** 1.6
Declare a recursive function sum: int * int  -> int, where
    sum(m,n)=m+(m+1)+(m+2)+...+(m+(n-1))+(m+n)
for m>=0 and n>=0. (Hint: use two clauses with (m,0) and (m,n) as patterns.)
***)
let rec sum1_6(m,n)=
    match (m,n) with
    | (m,0) when m>=0 -> m
    | (m,n) when m>=0 && n>0 -> m + n + sum1_6(m,n-1)
    | (_,_) -> failwith "m and n should bouth be larger or equal than 0.";;
sum1_6(2,3);;

(*** 2.8
The following figure gives the first part of Pascal's triangle:
    1
   1 1
  1 2 1
 1 3 3 1  
1 4 6 4 1
The entrise of the trianlle are called binomial  coefficients. The k'th binomial coefficient of the 
n'th row is denoted (n k) for n>=0 and 0<=k<=n. For example, (2 1) = 2 and (4 2) = 6. The first and 
the last binomial coefficents, that is, (n 0) and (n n), of row n are both 1. A binomial coefficient 
inside a row is the sum of the two binomial coefficients immediately above it. These properties can 
be expressed as follows:
    (n 0) = (n n) = 1
and 
    (n k) = (n-1 k-1) + (n-1 k) if n!=0, k!=0 and n>k.
Declare an F# function bin: int * int -> int to compute binomiol coefficients.
***)

let rec bino(n,k) =
    match (n,k) with
    | (n,k) when n>=0 && (k=0 || k=n) -> 1
    | (n,k) when n>0 && n>k -> bino(n-1,k-1) + bino(n-1,k)
    | (_,_) -> failwith "n and k should be both larger or equal than 0 and k should be not larger than n.";;

bino(4,2);;

(*** 4.7
Declare an F# function multiplicity x xs to find the number of times the value x occurs in the list xs.
***)
let rec multiplicity x xs =
    match xs with
    | [] -> 0
    | e::xt when e=x -> 1 + multiplicity x xt
    | _::xt -> multiplicity x xt;;
multiplicity 1 [1;0;1;0;1];;