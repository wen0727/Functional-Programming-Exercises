The command 
	RunFsc -a FILENAME1.fsi FILENAME2.fs

Outputs 
	FILENAME2.dll



(* Part 4 source code. *)
[<CustomEquality;CustomComparison>]
type Degree = 
    | MinusInf
    | Fin of int
    override d.ToString() =
        match d with
        | MinusInf -> "minus infinity"
        | Fin n -> if n>=0 then string n
                   else "n must be not negative number"
    override d.Equals dobj =
        match d with
        | MinusInf -> match dobj with 
                      | :? Degree as d1 -> d1=MinusInf
                      | _ -> false
        | Fin n -> match dobj with 
                   | :? Degree as d1 -> d1=Fin n
                   | _ -> false
    override d.GetHashCode() = hash (d)
    interface System.IComparable with 
        member d.CompareTo dobj =
            match dobj with
            | :? Degree as d2 -> compare d d2
            | _ -> invalidArg "dobj"
                              "Cannot compare values of different types."

let rec p2Deg = 
    function
    | [] -> 0
    | _::pt -> 1 + (p2Deg pt);;
              
let fDegreeP ps = 
    match ps with
    | [] -> MinusInf
    | _::pt -> Fin (p2Deg pt);;
let degree (P xs) = fDegreeP xs;;

let addD d1 d2 = 
    match (d1,d2) with
    | (MinusInf,_) | (_,MinusInf) -> MinusInf
    | (Fin N,Fin M) -> Fin (N+M);;

type Degree with
    static member (+) (d1, d2) = addD d1 d2


[<Sealed>]
type Degree = 
    interface System.IComparable
    static member (+) : Degree * Degree -> Degree 
val degree : Poly -> Degree

val ofList : int list -> Poly
val toList : Poly -> int list
val ofArray : int array -> Poly