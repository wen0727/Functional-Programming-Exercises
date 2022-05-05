(*MultiSet
    The MultiSet is represented as list of pairs e.g
        [(m0,e0);...;(m_(n),e_(n))]     where n is finite integer.
    where ei is the member of the multi-set and vi is the multiplicity of ei.

    For the multi-set we have an multi-set invariant such as
        ei not equal ej for i not equal to j

    Furthermore,
        The value of the member is a sequence of characters which doesn't contain the ASCII value of space.
        And the value of the multiplicity is integer.
    *)
//Invariant:
//MultiSet -> bool

let rec pForAll p xs = 
    match xs with
    | []        -> true
    | x::xt     -> p x && pForAll p xt;;

let rec pInvariant1 xs = 
    match xs with
    | []            -> true
    | (_,ei)::mt    -> pForAll (fun (_,ej) -> ei<>ej) mt && pProperty1 mt

//Multiplicity and Member insertion:
//string -> MultiSet -> Multi-set
let rec fInsertValueKey x =
    function
    | []              -> [(1,x)]
    | (value,y)::tail -> if x=y 
                         then (value+1,y)::tail
                         else (value,y)::fInsertValueKey x tail;;

//String to MultiSet.
//MultiSet -> string -> MultiSet -> MultiSet
let rec fPhrase acc word =
    function 
    | []    -> fInsertValueKey word acc
    | c::cs -> if c=' '
               then fPhrase (fInsertValueKey word acc) "" cs 
               else fPhrase acc (word+string c) cs;;
//example 1:
let example1 = fPhrase [] "" (Seq.toList "Go do that thing that you do so well");;
List.map (fun (v,k) -> printf "%d: %s" v k) example1;;

//Unit-test of example1's property.
let Test1 = pInvariant1 example1;;
printf "%b" Test1;; 

