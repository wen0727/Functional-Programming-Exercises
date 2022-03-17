(* Blackboard exercise: substitution float type expression 
only work for first order.
*)
type Fexpr = | Const of float
             | X
             | Add of Fexpr * Fexpr
             | Sub of Fexpr * Fexpr
             | Mul of Fexpr * Fexpr
             | Div of Fexpr * Fexpr;;

(* substX: Fexpr -> Fexpr -> Fexpr
so substX e e' is the expression obtained from e by substituting every occurencee of X with e' *)

let rec substX fe =
    function 
    | Const r -> Const r
    | X -> fe
    | Add(fe1,fe2) -> Add(substX fe fe1,substX fe fe2)
    | Sub(fe1,fe2) -> Sub(substX fe fe1, substX fe fe2)
    | Mul(fe1,fe2) -> Mul(substX fe fe1, substX fe fe2)
    | Div(fe1,fe2) -> Div(substX fe fe1, substX fe fe2);;

let ex = Add(Sub(X, Const 2.0), Mul(Const 4.0, X));;
substX (Div(X,X)) ex;;

(* Exercise: File System with extention *)
(* Mutual recursive type declaration *)
type FileSys = Element list
and Element = File of string*string
            | Dir of string*FileSys
let d1 = Dir("d1",[File("a1","java");
                   Dir("d2", [File("a2","fsx");
                              Dir("d3", [File("a3","fs")])]);
                   File("a4","fsx");
                   Dir("d3", [File("a5","pdf")])]);;

(* Declare mutually recursive fuctions: *)
(* Extract the list of all file names with extentions and names of directories occuring in the file systems and elements.  *)
let rec namesFileSys = 
    function
    | [] -> []
    | e::et -> namesElement e @ namesFileSys et
and namesElement =
    function
    | File (n1,n2) -> [n1 + "." + n2]
    | Dir (n,fs) -> n::namesFileSys fs;;

namesElement d1;;

(* Extract the set of all file names which the extention is "ext" in a file system of element.  *)
let rec searchFileSys ext filesys = 
    match filesys with
    | [] -> set []
    | e::et -> Set.union (searchElement ext e) (searchFileSys ext et) 
and searchElement ext elem =
    match elem with
    | File (n1,n2) -> if n2=ext then set [n1] else set []
    | Dir (_,fs) -> searchFileSys ext fs;;
searchElement "fsx" d1;;

(* Extract the all file names with full path *)

let rec fLongNamesFileSys pre filesys =
    match filesys with
    | [] -> set []
    | e::et -> Set.union (fLongNamesElement pre e) (fLongNamesFileSys pre et)
and fLongNamesElement pre e =
    match e with
    | File (n1,n2) -> set [pre + n1 + "." + n2]
    | Dir (n,fs) ->  fLongNamesFileSys (pre + n + "\\") fs;;

let longNamesFileSys filesys = fLongNamesFileSys "" filesys;;
let longNamesElement e = fLongNamesElement "" e;;

(* use Set.map to map from a name to prefix + name *)
let addDir d lns = Set.map (fun ln -> d + "\\" + ln) lns 
let rec longNamesElement1 =
      function
      | File(n,ext) -> Set.singleton(n+"."+ext)
      | Dir(d,fs)   -> let lns = longNamesFileSys1 fs
                       addDir d lns 
and longNamesFileSys1 = 
      function 
      | []    -> Set.empty
      | e::es -> Set.union (longNamesElement1 e) (longNamesFileSys1 es);;

(* Use List.fold to traverse list of elment and Set.union to union each full path name under the same directory *)
let rec lNE path =
      function
      | File(n,ext) -> Set.singleton(path + n+ "."+ext)
      | Dir(d,fs)   -> lNFS (path + d + "\\") fs
and lNFS path fs = 
      List.fold (fun lns e -> Set.union lns (lNE path e)) Set.empty fs;;

let longNamesElement2 e = lNE "" e;; 
let longNamesFileSys2 fs = lNFS "" fs;;
