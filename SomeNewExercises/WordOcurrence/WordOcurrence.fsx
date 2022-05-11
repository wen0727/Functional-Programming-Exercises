open System.IO
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
let rec pInvariant1 ms = 
    match ms with
    | []            -> true
    | (_,ki)::mt    -> List.forall (fun (_,kj) -> ki <> kj) mt && pInvariant1 mt

//Multiplicity and Member insertion:
//string -> MultiSet -> Multiset
let rec fInsertTermToList x ms =
    match ms with
    | []            -> [(1,x)]
    | (v,k)::mt     -> if x=k 
                       then (v+1,k)::mt
                       else (v,k)::fInsertTermToList x mt;;

//string -> Map<string,int> -> Map<string,int>
let fInsertTermToMap word ms = 
    match Map.tryFind word ms with
    | Some v -> Map.add word (v+1) ms
    | None -> Map.add word 1 ms;;

//String to MultiSet.
//MultiSet -> string -> MultiSet -> MultiSet
let pSpace c = c=' ' 
let rec fPhrase fG p word cList acc =
    match cList with
    | []        -> fG word acc
    | c::ct     -> if p c
                   then fPhrase fG p "" ct (fG word acc) 
                   else fPhrase fG p (word+string c) ct acc;;

//example 1:
let egCharList1 = (Seq.toList "Go do that thing that you do so well");;
let testExample1 = fPhrase fInsertTermToList pSpace "" egCharList1 [];;
List.iter (fun (v,k) -> printf "%d: %s\n" v k) testExample1;;

//example 2:
let testExample2 = fPhrase fInsertTermToMap pSpace "" egCharList1 Map.empty;;
List.iter (fun (k,v) -> printf "%d: %s\n" v k) (Map.toList testExample2);;
//Unit-test of example1's property.
let Test1 = pInvariant1 testExample1;;

printf "%b" Test1;; 

//realative path
let datapath = @"data\data.txt";;

//File Input
//Make a collection by applying function to the accumulator until EOS.
let fLineFold fG acc path =
    use SR = File.OpenText path
    let rec fFold res =
        if SR.EndOfStream then res
        else fFold (fG res SR)
    let foldFrom = fFold acc
    SR.Close()
    foldFrom;;
//File to MultiSet
let fFileToMultiSet fG acc path =
    fLineFold (fun ms res -> fG "" (Seq.toList (res.ReadLine())) ms) acc path;;

//example3, convert the file to the term list.
let example3 = fFileToMultiSet (fPhrase fInsertTermToList pSpace) [] datapath;;
//example4,                         Map of terms.
let example4 = fFileToMultiSet (fPhrase fInsertTermToMap pSpace) Map.empty datapath;;

//Convert list of term to string
let rec fMSListToString acc terms = 
    match terms with
    | []        -> acc
    | (v,k)::xt -> fMSListToString (acc + string v + ": " + k + "\n") xt;;

let fMSMapToString acc terms =
    Map.foldBack(fun k v res -> string v + ": " + k + "\n" + res ) terms acc;;

//File Output
let fMSListToFile path ms =
    use outPutFile = File.CreateText path
    outPutFile.Write (fMSListToString "" ms)
    outPutFile.Close();;

let path1 = "data\dataOuput1.txt"
let example5 = fMSListToFile path1 example3;;

let fMSMapToFile path ms =
    use outPutFile = File.CreateText path
    outPutFile.Write (fMSMapToString "" ms)
    outPutFile.Close();;

let path2 = "data\dataOuput2.txt"
let example6 = fMSMapToFile path2 example4;;
