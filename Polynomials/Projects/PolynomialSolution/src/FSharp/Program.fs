open System
let printNumbers ns =
    let _ = List.iter (fun n -> Console.Write (string n + " ")) ns
    Console.WriteLine ""
[<EntryPoint>]
let main argv =
    let p1 = Polynomial.ofList [1; 0; -3]
    let p2 = Polynomial.ofList [0; 0; -2]
    let p3 = p1 + p2 * p1
    let p4 = p3 - p3
    let d3 = Polynomial.degree p3
    let d4 = Polynomial.degree p4
    let _ = Console.WriteLine("p1(x) is " + string p1)
    let _ = Console.WriteLine("p2(x) is " + string p2)
    let _ = Console.WriteLine("p3(x) is " + string p3)
    let _ = Console.WriteLine("p4(x) is " + string p4)
    let _ = Console.WriteLine("Degree of p3(x) is " + string d3)
    let _ = Console.WriteLine("Degree of p4(x) is " + string d4)
    let _ = Console.Write("Coefficients of p3(x) are ")
    let _ = printNumbers(Polynomial.toList p3)
    let _ = Console.WriteLine("p3'(x) is " + string(Polynomial.derivative p3))
    let ns = Polynomial.toList(Polynomial.compose p1 p2)
    let _ = Console.Write "Coefficients of p1(p2(x)) are "
    let _ = printNumbers ns
    let _ = Console.ReadKey()
    0 // return an integer exit code