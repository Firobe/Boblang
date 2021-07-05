open Utils

let expand_known_types t =
  List.fold_left (fun e (id, v) -> tsubstitute id v e) t

let tyexpand_everything tyenv matyenv t =
  let rec expand_tmacros = function
    | TUnit -> TUnit
    | TMacro (id, tl) ->
      begin match List.find_opt (fun (mid, _, _) -> mid = id) matyenv with
        | None ->
          List.iter (fun (mid, _, _) -> Printf.printf "Got %s\n" mid) matyenv;
          failwith ("Typemacro " ^ id ^ " unknown")
        | Some (_, params, body) ->
          let tl' = List.map expand_tmacros tl in
          let plen = List.length params in
          let tlen = List.length tl' in
          if plen = tlen then
            List.fold_left2 (fun a b c -> tsubstitute b c a) body params tl
          else
            failwith (Format.sprintf
                        "Macro %s expected %d arguments but got %d"
                        id plen tlen)
      end
    | (TVar _) as v -> v
    | TArrow (tau1, tau2) -> 
      TArrow (expand_tmacros tau1, expand_tmacros tau2)
    | TComp tau -> TComp (expand_tmacros tau)
    | TSum (tau1, tau2) -> TSum (expand_tmacros tau1, expand_tmacros tau2)
    | TProduct (tau1, tau2) -> TProduct (expand_tmacros tau1, expand_tmacros tau2)
    (*| (TRecursive (id, _)) as r when id = f -> r*)
    | TRecursive (id, tau) -> TRecursive (id, expand_tmacros tau)
  in
  let t' = expand_tmacros t in
  expand_known_types t' tyenv

let expand_types_in_term tyenv matyenv =
  let te = tyexpand_everything tyenv matyenv in
  let rec aux = function
  | Unit -> Unit
  | (Variable _) as v -> v
  | Computation t -> Computation (aux t)
  | Abstraction (t, id, e) -> Abstraction (te t, id, aux e)
  | Return t -> Return (aux t)
  | Force t -> Force (aux t)
  | Bind (e1, id, e2) -> Bind (aux e1, id, aux e2)
  | Application (e1, e2) -> Application (aux e1, aux e2)
  | Left (t, e) -> Left (te t, aux e)
  | Right (t, e) -> Right (te t, aux e)
  | Case (e, x1, e1, x2, e2) -> Case (aux e, x1, aux e1, x2, aux e2)
  | Tuple (e1, e2) -> Tuple (aux e1, aux e2)
  | Split (e, x1, x2, e') -> Split (aux e, x1, x2, aux e')
  | Fold (t, e) -> Fold (te t, aux e)
  | Unfold t -> Unfold (aux t)
  | Macro (id, ttl, tl) -> Macro (id, List.map te ttl, List.map aux tl)
  | Print_char t -> Print_char (aux t)
  in aux

let expand_known_terms t =
  List.fold_left (fun e (id, v) -> substitute id v e) t

let texpand_everything tenv tyenv matenv matyenv t =
  let matenv = ("SUBSTITUTE", [], [], Unit) :: matenv in
  let rec expand_macros = function
    | Macro (id, ttl, tl) ->
      begin match List.find_opt (fun (mid, _, _, _) -> mid = id) matenv with
      | None -> failwith ("Macro " ^ id ^ " unknown")
      | Some (_, type_names, term_names, body) ->
        let tl' = List.map expand_macros tl in
        let ttl' = List.map (tyexpand_everything tyenv matyenv) ttl in
        let res = if id = "SUBSTITUTE" then
            begin match tl' with
              | [Variable n; tot; intt] ->
                substitute n tot intt
              | _ -> failwith "SUBSTITUTE wrongly applied"
            end
        else
          let plen = List.length term_names in
          let tlen = List.length tl' in
            if plen = tlen then
              let applied = List.fold_left2 (fun a b c -> substitute b c a)
                  body term_names tl' in
              expand_macros applied
            else
              failwith (Format.sprintf
                          "Macro %s expected %d arguments but got %d"
                          id plen tlen)
        in
        let assoc = List.map2 (fun a b -> (a, b)) type_names ttl' in
        expand_types_in_term (tyenv @ assoc) matyenv res
      end
    | Unit -> Unit
    | (Variable _) as v -> v
    | Computation t -> Computation (expand_macros t)
    | Abstraction (t, id, e) -> Abstraction (t, id, expand_macros e)
    | Return t -> Return (expand_macros t)
    | Force t -> Force (expand_macros t)
    | Bind (e1, id, e2) -> Bind (expand_macros e1, id, expand_macros e2)
    | Application (e1, e2) -> Application (expand_macros e1, expand_macros e2)
    | Left (t, e) -> Left (t, expand_macros e)
    | Right (t, e) -> Right (t, expand_macros e)
    | Case (e, x1, e1, x2, e2) ->
      Case (expand_macros e, x1, expand_macros e1, x2, expand_macros e2)
    | Tuple (e1, e2) -> Tuple (expand_macros e1, expand_macros e2)
    | Split (e, x1, x2, e') -> Split (expand_macros e, x1, x2, expand_macros e')
    | Fold (t, e) -> Fold (t, expand_macros e)
    | Unfold t -> Unfold (expand_macros t)
    | Print_char t -> Print_char (expand_macros t)
  in
  let t' = expand_macros t in
  let t'' = expand_known_terms t' tenv in
  expand_types_in_term tyenv matyenv t''

let print_position fmt lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  Format.fprintf fmt "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse fn =
  let inx = open_in fn in
  let lexbuf = Lexing.from_channel inx in
  let res = try Bobgram.program Boblex.read lexbuf
    with Bobgram.Error -> 
      Format.printf "%a: syntax error\n" print_position lexbuf;
      exit (-1)
  in close_in inx; res
