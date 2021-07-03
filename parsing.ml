open Utils

let expand_known_types t =
  List.fold_left (fun e (id, v) -> tsubstitute id v e) t

let tyexpand_everything tyenv matyenv t =
  let t' = expand_known_types t tyenv in
  let rec tymapply ((f, params, r) as w) = function
    | TUnit -> TUnit
    | TMacro (id, tl) ->
      let tl' = List.map (tymapply w) tl in
      if id = f then
        let plen = List.length params in
        let tlen = List.length tl in
        if plen = tlen then
          List.fold_left2 (fun a b c -> tsubstitute b c a) r params tl
        else
          failwith (Format.sprintf
                      "Macro %s expected %d arguments but got %d"
                      id plen tlen)
      else TMacro (id, tl')
    | (TVar _) as v -> v
    | TArrow (tau1, tau2) -> 
      TArrow (tymapply w tau1, tymapply w tau2)
    | TComp tau -> TComp (tymapply w tau)
    | TSum (tau1, tau2) -> TSum (tymapply w tau1, tymapply w tau2)
    | TProduct (tau1, tau2) -> TProduct (tymapply w tau1, tymapply w tau2)
    | (TRecursive (id, _)) as r when id = f -> r
    | TRecursive (id, tau) -> TRecursive (id, tymapply w tau)
  in List.fold_left (fun e w -> tymapply w e) t' matyenv

let expand_known_terms t =
  List.fold_left (fun e (id, v) -> substitute id v e) t

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

let texpand_everything tenv tyenv matenv matyenv t =
  let t' = expand_known_terms t tenv in
  let rec tmapply ((f, tparams, params, r) as w) = function
    | Macro (id, ttl, tl) ->
      let tl' = List.map (tmapply w) tl in
      let ttl' = List.map (tyexpand_everything tyenv matyenv) ttl in
      if id = f then
        if f = "SUBSTITUTE" then
          begin match tl' with
            | [Variable n; tot; intt] ->
              substitute n tot intt
            | _ -> failwith "SUBSTITUTE wrongly applied"
          end
        else
        let plen = List.length params in
        let tlen = List.length tl' in
        let r' =
          if plen = tlen then
            List.fold_left2 (fun a b c -> substitute b c a) r params tl'
          else
            failwith (Format.sprintf
                        "Macro %s expected %d arguments but got %d"
                        id plen tlen)
        in
        let assoc = List.map2 (fun a b -> (a, b)) tparams ttl' in
        expand_types_in_term assoc [] r'
      else Macro (id, ttl', tl')
    | Unit -> Unit
    | (Variable _) as v -> v
    | Computation t -> Computation (tmapply w t)
    | Abstraction (t, id, e) -> Abstraction (t, id, tmapply w e)
    | Return t -> Return (tmapply w t)
    | Force t -> Force (tmapply w t)
    | Bind (e1, id, e2) -> Bind (tmapply w e1, id, tmapply w e2)
    | Application (e1, e2) -> Application (tmapply w e1, tmapply w e2)
    | Left (t, e) -> Left (t, tmapply w e)
    | Right (t, e) -> Right (t, tmapply w e)
    | Case (e, x1, e1, x2, e2) -> Case (tmapply w e, x1, tmapply w e1, x2, tmapply w e2)
    | Tuple (e1, e2) -> Tuple (tmapply w e1, tmapply w e2)
    | Split (e, x1, x2, e') -> Split (tmapply w e, x1, x2, tmapply w e')
    | Fold (t, e) -> Fold (t, tmapply w e)
    | Unfold t -> Unfold (tmapply w t)
    | Print_char t -> Print_char (tmapply w t)
  in
  let t'' = List.fold_left (fun e w -> tmapply w e) t' matenv in
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
