open System.IO
open System.Text.RegularExpressions;;
(*MultiSet
    The MultiSet is represented as list of pairs e.g
        [(m0,e0);...;(m_(n),e_(n))]     where n is finite integer.
    where ei is the member of the multi-set and vi is the multiplicity of ei.

    For the MultiSet we have an MultiSet invariant such as
        ei not equal ej for i not equal to j

    Furthermore,
        The value of the member is a sequence of characters which doesn't contain the ASCII value of space.
        And the value of the multiplicity is integer.
    *)
//Invariant:
//MultiSet -> bool

let rec pInvariant1 xs = 
    match xs with
    | []            -> true
    | (_,ei)::mt    -> List.forall (fun (_,ej) -> ei<>ej) mt && pInvariant1 mt

//Multiplicity and Member insertion:
//string -> MultiSet -> Multi-set
let rec fInsertValueKey x =
    function
    | []            -> [(1,x)]
    | (k,e)::tail   -> if x=e 
                       then (k+1,e)::tail
                       else (k,e)::fInsertValueKey x tail;;

//String to MultiSet.
//MultiSet -> string -> MultiSet -> MultiSet
let rec fPhrase fG cList word acc =
    match cList with
    | []        -> fG word acc
    | c::tail   -> if c=' '
                   then fPhrase fG tail "" (fG word acc) 
                   else fPhrase fG tail (word+string c) acc;;

//example 1:
let example1 = fPhrase fInsertValueKey (Seq.toList "Go do that thing that you do so well") "" [];;
List.map (fun (v,k) -> printf "%d: %s" v k) example1;;

//Unit-test of example1's property.
let Test1 = pInvariant1 example1;;
printf "%b" Test1;; 


let datapath = @"data\data.txt";;

let fLineFold fG acc path =
    use SR = File.OpenText path
    let rec fFold res =
        if SR.EndOfStream then res
        else fFold (fG res SR)
    let foldFrom = fFold acc
    SR.Close()
    foldFrom;;

let fFileToMultiSet acc path =
    fLineFold (fun ms res -> fPhrase fInsertValueKey (Seq.toList (res.ReadLine())) "" ms) acc path;;


