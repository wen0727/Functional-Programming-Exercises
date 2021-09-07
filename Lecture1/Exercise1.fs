(* Blackboard exercise *)
let rec memberOf x ys =
    match ys with 
    | [] -> true
    | y::yt -> x=y || memberOf x yt
