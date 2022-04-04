#time
(* Make a function for the sequence of odd numbers *)
let natN = Seq.initInfinite id;;                //delayed Seq<int>
let oddN = Seq.filter (fun n -> n%2=1) natN;;   //natN is delayed until theyare demanded by Seq.filter function.
//let oddN = Seq.initInfinite (fun i -> 2*i+1);;

let cons x sq = Seq.append (Seq.singleton x) sq;;
let rec from i = cons i (from(i+1));;

(* Evaluation of from 47 would cause crash.
   The lazy sequence(call by need) cons produced is conflict with   
    f# eager evaluation(call by value) which results infinite
    recursive unfolding of the function from.

   Delay 
    fun () -> 3+4   //delay for pusing the value stored in the heap
    it ()           //return the first value in the stack
   
   Seq.delay: (unit -> seq<'a>) -> seq<'a> 

   Seq.cache: seq<'a> -> seq <'a>
   A cached sequence remembers the already computed sequence
   which avoids re-computation.

*)
let rec from1 i = Seq.delay (fun () -> cons i (from1(i+1)));;
from1 11;;

(* Make a function for the sequence of numbers 
    1,1,2,6,...,n!,...
*)
let rec factA acc =
    function
    | 0 -> acc
    | n when n>0 -> factA (n*acc) (n-1)
    | _ -> failwith "n must be not a negative number.";;

let ffactA n = factA 1 n;;
(* Cache avoid recomputation, *)
let seqFactL = Seq.map (fun n -> ffactA n) natN;; 
seqFactL;;
(* seq expression have delay implicitly. *)
let seqFactE = seq {
                for i in natN
                    do yield ffactA i
               };;
seqFactE;;
(* Make a function for the sequence of integers
    1,1,2,6,...,n!,...
   but this time, use a formular such that
    i_0=f(0), i1=f(0)*1, i2=f(1)*2
    ...
    i_n=f(n-1)*n
*)
let ffactNext n = 
    match n with
    | 0 -> 1
    | n when n>0 -> (Seq.item (n-1) seqFactL) * n
    | _ -> failwith "n must be not a negative number.";;

ffactNext 6;;
let seqFact1L = Seq.initInfinite (fun i -> ffactNext i);;
seqFact1L;;

let seqFact1E = 
    seq {
        for i in natN do
             if i=0 then 1
             else i* Seq.item (i-1) seqFactE
    }
seqFact1E;;

(* Make a function to denote the following integers 
    0,-1,1,-2,2,-3,3,...
*)
let zNP = seq {
                for i in natN
                    do if i=0 
                       then yield 0
                       else yield! seq [-i;i]
                   }
zNP;;

(* Collatz conjecture 
    consider a sequence generated from a positive number n as:
        a0 a1 a2 a3 ... ai ...
    where a0 = n and
          ai = a_(i-1) / 2          if a_i-1 is even
               3 * a_(i-1) + 1      if a_i-1 is odd

    e.g. the first 8 elements of function of n for n = 1,2,3,4 are
            n=1 :   1   4   2   1   4   2   1   4
            n=2 :   2   1   4   2   1   4   2   1
            n=3 :   3   10  5   16  8   4   2   1
            n=4 :   4   2   1   4   2   1   4   2
*)
(* Make a function collatz: int -> seq<int> for n>0 represents
    collatz sequence starting with n.
    n  = 1
    i = 0    a0 = n                                        1
    i = 1    a0 is odd      a1 = 3 * n + 1                 4
    i = 2    a1 is even     a2 = (3 * n + 1)  / 2          2
    i = 3    a2 is even     a3 = ((3 * n + 1)  / 2) / 2    1
     ...
    
    f(n) = n/2      if n mod 2 = 0
         = 3n+1     if n mod 2 = 1

    ith number is f(n)^i
*)
let rec fCollatz n i = 
    match i with
    | 0 -> n
    | j when j>0 && (fCollatz (n) (j-1))%2=0 -> (fCollatz (n) (j-1))/2
    | j when j>0 && (fCollatz (n) (j-1))%2=1 -> 3 * (fCollatz (n) (j-1)) + 1
    | _ -> failwith "n must be non negative number.";;

fCollatz 3 4;;
fCollatz 1 3;;
let collatz n = 
    seq {
        for i in natN do
            yield fCollatz n i
    };;
collatz 1;;

(* Tail-recursive version *)
let rec fCollatzA n acc i = 
    match i with
    | 0 -> acc
    | j when j>0 && acc%2=0 -> fCollatzA n (acc/2) (j-1)
    | j when j>0 && acc%2=1 -> fCollatzA n (3*acc+1) (j-1)
    | _ -> failwith "n must be non negative number.";;

let collatzA n = 
        seq {
            for i in natN do
                yield fCollatzA n n i
    };;
collatzA 3;;

(* Make a sequence collatazSequence: seq<seq<int>> represents
    the sequence of collatz sequence, such as
    collatz(1)  collatz(2)  collatz(3) ...
*)
let collatzSequence = 
        seq {
            for i in natN do
                yield collatzA(i+1)
        };;
collatzSequence;;

(* Make a sequence stoppingTime: seq<int> where the element 
    ti is the stopping time of collatz(i+1). 
    e.g. for n=4 the sequence is 
    seq [0;1;7;2]
*)    
(* Home made index function which matching the pattern *)
let rec fCTime acc sq =
    match Seq.item acc sq with
    | 1 -> acc
    | _ -> fCTime (acc+1) sq 
let stoppingtime1 = 
    seq {
        for i in collatzSequence do
            yield fCTime 0 i
    }
stoppingtime1;;
(* Use library function to get index *)
let stoppingTime =
        seq {
            for i in collatzSequence do
                yield Seq.findIndex (fun j -> j=1) i
        };;
stoppingTime;;
Seq.take 20 stoppingTime;;

(* Make a maxStoppingTimes function to compute a sequence such
    as m0 m1 m2 ... mi ...
   let ti, i>=0 denote the elements of stoppingTime
   where m0 is t0
         m1 is the bigger value between previous bigger value m0 and current time t1, 
         m2 is the bigger value between previous bigger value m1 and t2
         m3 is the bigger value between m2 and 
*)
(* recursively linking head of sequence with tail
    requires delay, for lazy sequence
*)
let rec fMaxHead cm sq =
    Seq.delay (fun () ->
        let s0 = Seq.item 0 sq
        cons (max cm s0) (fMaxHead (max cm s0) (Seq.tail sq)));;

let maxStoppingTimes1 = fMaxHead 0 stoppingTime;;
maxStoppingTimes1;;

(* Library functions *)
let maxStoppingTimes = 
    Seq.scan (fun acc x -> 
        max x acc) 0 (Seq.skip 1 stoppingTime)
maxStoppingTimes;;

(* Consider following expressions and give types, value and waht 
the function computes.
*)
let sq = Seq.initInfinite (fun i -> 3*i);;
let k j = 
    seq {
        for i in sq do
            yield (i,i-j)    
    };;
k 2;;
(* 

    sq 
     is a value identifier, Seq.initInfinite is a library function
     that generates (call by need ~ infinite) sequence. 

     The value expression sq can be typed with fresh label
      such as below:
        sq:T1   
     
     Since Seq.initInfinite is type of
        (int->'a) -> Seq<'a>
     
     Then i and 3*i are type of int. Now we can unify the types as:
        T1=Seq<int>
     
     In F#, sq has most general type as:
        sq: (int -> int) -> Seq<int>
     
     The function computes multiple of 3.

    k 
     1.The function has one argument and we can tag the argument with 
     fresh label such as:
        j : T1

     2.The value expression can be labeled as:
        i-j: int
        k j : (int -> int*int) -> Seq<int*int>

     3.Now we can unify the type as below:
        T1=int
     4.In F#, k has most general type such as:
        k: int -> (int -> int*int) -> Seq<int*int>

     What they computes?
     sq:
      sq computes sequence of elements of multiple of 3
        3*0,3*1,3*2 ... 3*n
     
     k: 
      k computes sequence of pair
        (3*0,0-j),(3*1,1-j), (3*2,2-j) ... (3*n,n-j),

*)

(* Consider following expressions 
    give the value of those expressions.
*)
let xs14 = Seq.toList (Seq.take 4 sq);;
let ys14 = Seq.toList (Seq.take 4 (k 2));;
(* 
    xs = [0;3;6;9]

    ys = [(0,-2);(3,1);(6,4);(9,7)]

*)

(* Make a function: 
    multTable: int -> seq<int> 
   so multTable n gives the sequence of the first 10 numbers 
   in the table for n.
    e.g. multTable 3 = seq [3;6;9;12;...;30]
*)
let multTable n = 
    Seq.take 10 (
        seq {
            for i in natN do
                yield (i+1)*n
        });;
multTable 3;;
(* Make a function 
    tableOf: int -> int -> (int -> int -> 'a) -> seq<int*int*'a> 
*)
let tableOf m n f =
    seq {
        for i in (Seq.take m oddN) do
            for j in (Seq.take n natN) do
                yield! [(i,j+1,f i (j+1))]
    };;

tableOf 3 4 (+);;
let tableOf1 m sq = Seq.filter (fun i -> i<m) sq;;  //ok to define
tableOf1 3 oddN;;                                   //heap is exausted, run out memory
let rec conA acc =
    function 
    | 0 -> acc
    | n when n>0 -> conA ("a"+acc) (n-1)
    | _ -> failwith "The argument must be non-negative.";;
let infA = 
    seq {
        for i in natN do
            conA ("") (i+1)
    };;
infA;;