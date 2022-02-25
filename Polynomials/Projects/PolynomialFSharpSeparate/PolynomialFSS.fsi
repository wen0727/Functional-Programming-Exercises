module Polynomial
[<Sealed>]
type Poly = 
    static member ( + ) : Poly * Poly -> Poly
    static member ( - ) : Poly * Poly -> Poly
    static member ( * ) : int * Poly -> Poly
    static member ( * ) : Poly * Poly -> Poly

val eval : int -> Poly -> int
val derivative : Poly -> Poly
val compose : Poly -> Poly -> Poly
val ofList : int list -> Poly
val toList : Poly -> int list
val ofArray : int [] -> Poly

[<Sealed>]
type Degree = 
    interface System.IComparable
    static member (+) : Degree * Degree -> Degree
val degree : Poly -> Degree

