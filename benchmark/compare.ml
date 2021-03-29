let space = Str.regexp (Str.quote " ")

let parse_lines o = 
  let rec parse acc = 
    match input_line o with
    | x -> parse ((Str.split space x)::acc)
    | exception End_of_file -> List.rev acc in
  parse []

let select_success l =
  List.filter (List.mem "(success)") l

let rec take n l =
  match n with
  | 0 -> []
  | n -> match l with
         | [] -> []
         | e::l -> e::(take (n-1) l)

let check_succ p l =
  let rec check_succ n l = 
    match l with
    | [] -> None
    | [e] -> Some(n,e,e)
    | e1::e2::l -> if p e1 e2 then check_succ (n+2) l else (Some(n,e1,e2)) in
  check_succ 0 l
                                                            

let parse_numbers o =
  let rec parse acc = 
    match input_line o with
    | x -> parse (float_of_string x::acc)
    | exception End_of_file -> List.rev acc in
  parse []

let sum_compare l1 l2 =
  let rec sum l e g l1 l2 = 
    match l1, l2 with
    | [] , [] -> (l,e,g)
    | v1::l1 , v2::l2 ->
       begin
       match compare v1 v2 with
       | 0 -> sum l (e+1) g l1 l2
       | -1 -> sum (l+1) e g l1 l2
       | _  -> sum l e (g+1) l1 l2
       end
    | _ , _ -> failwith "File should be of same length"
  in
  sum 0 0 0 l1 l2


let sum l =
  List.fold_left (+.) 0. l

let max l =
  List.fold_left max 0. l

let min l =
  List.fold_left min 0. l

module M = Map.Make(Float)

let group_by l =
  let rec group_by m l =
    match l with
      [] -> m
    | e::l -> let v = try M.find e m with Not_found -> 0 in
              group_by (M.add e (v+1) m) l in
  M.bindings (group_by M.empty l)


let output_groups l =
  List.iter (fun (i,j) ->
      Printf.printf "%f %i\n" i j) l

let output_list o l =
  List.iter (fun v -> Printf.fprintf o "%f " v) l

let speedup l1 l2 =
  List.fold_left2 (fun acc f1 f2 ->
      let res = f1 /. f2 in
      match classify_float res with
      | FP_normal -> res::acc
      | _         -> Printf.printf "Ignoring %f / %f = %f\n" f1 f2 res ; acc) [] l1 l2

let split_3 l1 l2 = 
  let rec split_3 (l,slm,slM) (e,sem,seM) (g,sgm,sgM) l1 l2 =
    match l1, l2 with
    | [] , [] -> ((l,slm,slM), (e,sem,seM), (g,sgm,sgM))
    | e1::l1 , e2::l2 ->
       if abs_float (e2 -. e1) <= 0.001
       then split_3 (l,slm,slM) (e+1,sem +. e1, seM+. e2) (g,sgm,sgM) l1 l2 
       else
         (match compare e1 e2 with
          | 0 -> split_3 (l,slm,slM) (e+1,sem +. e1, seM +. e2) (g,sgm,sgM) l1 l2 
          | -1 -> split_3 (l+1,slm+.e1,slM+.e2) (e,sem,seM) (g,sgm,sgM) l1 l2
          | _  -> split_3 (l,slm,slM) (e,sem,seM) (g+1,sgm+.e1,sgM+.e2) l1 l2)
    | _ , _ -> failwith "split_3 expects list of same size"
  in
  split_3 (0,0.,0.) (0,0.,0.) (0,0.,0.) l1 l2


let output_split_3 ((l,slm,slM), (e,sem,seM), (g,sgm,sgM))  =
  Printf.printf "<: %i (%f,%f)\n" l slm slM;
  Printf.printf "=: %i (%f,%f)\n" e sem seM;
  Printf.printf ">: %i (%f,%f)\n" g sgm sgM


  

let output_floats l =
  List.iter (fun x -> Printf.printf "%f " x) l;
  output_string stdout "\n"

(*
let _ =
  let f1 = Sys.argv.(1) in
  let f2 = Sys.argv.(2) in
  let l1 = parse_numbers (open_in f1) in
  let l2 = parse_numbers (open_in f2) in
  let speed = speedup l1 l2 in
  let min = min speed in
  let max = max speed in
  group_by ((max -. min) /. 10.) speed
 *)

let check e1 e2 =
  (List.mem "Lia" e1) && (List.mem "ILia" e2)
  ||
    (List.mem "Tauto" e1) && (List.mem "Itauto" e2)
  ||
    (List.mem "T1" e1) && (List.mem "T2" e2)


type ('a, 'b) res = Result of 'a | Error of 'b 

let filter p0 p1 l =
  let pi i x =
    let p = if i = 0 then p0  else p1 in
    let r = p x in
    r
  in

  let rec keep_only_last p n e l =
    match l with
    | [] -> (n,e,l)
    | e1:: l' -> if p e1 then keep_only_last p (n+1) e1 l' else  (n,e,l) in

  let rec filter n i l = 
    match l with
    | [] -> Result []
    | e1::l -> if pi i e1
               then
                 begin
                 let (n,e',l) = keep_only_last (pi i) (n+1) e1 l in
                 match filter n ((i+1) mod 2) l with
                 | Error b -> Error b
                 | Result l -> Result (e'::l)
                 end
               else Error (n,e1) in
  filter 0 0 l

                  

let select_at i l =
  List.map (fun x -> List.nth x i) l

let rec output_strings o l =
  match l with
  | [] -> output_string o "\n"
  | [e] -> output_string o e
  | [e1;e2] -> Printf.printf "%s|%s" e1 e2
  | e1::e2::l -> Printf.printf "%s|%s|" e1 e2 ; output_strings o l




let unzip_succ  l =
  let rec unzip l1 l2 l =
    match l with
    | [] -> (l1,l2)
    | [e] -> failwith "unzip_succ odd number of elements"
    | e1::e2::l -> unzip (e1::l1) (e2::l2) l in
  unzip [] [] l


let _ =
  let f1 = Sys.argv.(1) in
  let l = parse_lines (open_in f1) in
  Printf.printf "Parsing done\n";
  let s = select_success l in
  Printf.printf "Select done\n";
  let p0 x = List.mem "Tauto" x || List.mem "T1" x || List.mem "Lia" x in
  let p1 x = List.mem "Itauto" x || List.mem "T2" x || List.mem "ILia" x in
  let s = List.filter (fun x -> p0 x || p1 x) s in
  match filter p0 p1 s with
  | Error(n,ln) -> Printf.printf "Error at line %i %a\n" n output_strings ln
  | Result l -> 
     match check_succ check l with
     | Some(n,s1,s2) -> Printf.printf "Error at line %i %a %a\n" n output_strings s1 output_strings s2
     | None ->
        let s = select_at 5 l in
          let l1,l2 = unzip_succ s in
          let l1 = List.map float_of_string l1 in
          let l2 = List.map float_of_string l2 in
          let s = split_3 l2 l1 in
          output_split_3 s;
          let l1' = take 10 (List.rev (List.sort compare l1)) in
          let l2' = take 10 (List.rev (List.sort compare l2)) in
          Printf.printf "Worst historic %a\n" output_list l1';
          Printf.printf "Worst itauto %a\n" output_list l2';
          Printf.printf "Historic sum %f\n" (sum l1);
          Printf.printf "Itauto sum %f\n" (sum l2)
     
