open Utils

(* STATICS *)

let typecheck =
  let rec aux env tt =
    let term_error msg =
      Format.printf "Term was:@.%a@.Error: %s@." pp_term tt msg;
      failwith "Typing error"
    in match tt with
  | Unit -> (TUnit, JValue)
  | Variable v ->
    begin match List.assoc_opt v env with
      | None -> term_error ("Variable " ^ v ^ " is not bound")
      | Some t -> (t, JValue)
    end
  | Computation t ->
    let tau, j = aux env t in
    if j = JComp then (TComp tau, JValue)
    else term_error "lazy() expects a computation"
  | Abstraction (tau, id, t) ->
    let tau', j = aux ((id, tau) :: env) t in
    if j = JComp then (TArrow (tau, tau'), JValue)
    else (
      term_error "Abstractions should return computations"
    )
  | Return t ->
    let tau, j = aux env t in
    if j = JValue then (tau, JComp)
    else term_error "Only values can be returned"
  | Force t ->
    begin match aux env t with
      | TComp tau, JValue -> (tau, JComp)
      | _ -> term_error "Force should be on a lazy type"
    end
  | Bind (e1, id, e2) ->
    let tau, j = aux env e1 in
    if j = JComp then
      let tau', j' = aux ((id, tau) :: env) e2 in
        if j' = JComp then (tau', JComp)
        else term_error "Bind should return a computation"
    else term_error "Bind should be on computations"
  | Application (e1, e2) ->
    begin match aux env e1 with
      | TArrow (tau, tau'), JValue ->
        let tau'', j = aux env e2 in
        if j = JValue then
          if tau'' = tau then (tau', JComp)
          else (
            let msg = Format.asprintf "Incompatible types during application.
            Expected %a@, but got %a." pp_ttype tau pp_ttype tau'' in
            term_error msg
          )
        else term_error "Functions only applicable to values"
      | _ -> term_error "Can only apply functional values"
    end
  | Left (TSum (tau1, tau2), e) ->
    let tau'', j = aux env e in
    if j = JValue then
      if tau'' = tau1 then (TSum (tau1, tau2), JValue)
      else term_error "Wrong annotation in left"
    else term_error "Left expects a value"
  | Left _ -> term_error "Left expects a sum type annotation"
  | Right (TSum (tau1, tau2), e) ->
    let tau'', j = aux env e in
    if j = JValue then
      if tau'' = tau2 then (TSum (tau1, tau2), JValue)
      else term_error "Wrong annotation in right"
    else term_error "Right expects a value"
  | Right _ -> term_error "Right expects a sum type annotation"
  | Case (e, x1, e1, x2, e2) ->
    begin match aux env e with
      | TSum (tau1, tau2), JValue ->
        let tau, j' = aux ((x1, tau1) :: env) e1 in
        let tau', j'' = aux ((x2, tau2) :: env) e2 in
        if tau = tau' then
          if j' = JComp then
            if j'' = JComp then (tau, JComp)
            else term_error "Second branch of case is not a comput"
          else term_error "First branch of case is not a comput"
        else term_error "Branches in case do not have the same type"
      | t, _ -> term_error
               (Format.asprintf "Case expects a value of type sum, got %a" pp_ttype t)
    end
  | Tuple (v1, v2) ->
    let tau1, j1 = aux env v1 in
    let tau2, j2 = aux env v2 in
    if j1 = JValue then
      if j2 = JValue then (TProduct (tau1, tau2), JValue)
      else term_error "Second component of tuple must be a value"
    else term_error "First component of tuple must be a value"
  | Split (e, x1, x2, e') ->
    begin match aux env e with
      | TProduct (tau1, tau2), JValue ->
        let tau, j = aux ((x1, tau1) :: (x2, tau2) :: env) e' in
        if j = JComp then (tau, JComp)
        else term_error "Result of split should a computation"
      | _ -> term_error "Split expects a value of type product"
    end
  | Unfold e ->
    begin match aux env e with
      | TRecursive (id, tau) as rect, JValue ->
        tsubstitute id rect tau, JComp
      | _ -> term_error "Unfold expects a recursive value"
    end
  | Fold (TRecursive(id, tau), e) ->
    let rect = TRecursive (id, tau) in
    let tau', j = aux env e in
    if j = JValue then
      if tau' = tsubstitute id rect tau
      then rect, JValue
      else (
        Format.printf "Fold types do not correspond:@,%a@,and@,%a@,"
          pp_ttype tau' pp_ttype (tsubstitute id rect tau);
        term_error "Good luck with that"
      )
    else term_error "Fold expects a value"
  | Fold _ -> term_error "Fold expect a recursive type annotation"
  | Macro (n, _, _) -> term_error ("Macro " ^ n ^ " not expanded")
  | Print_char e ->
    begin match aux env e with
      | TRecursive (id1, TSum(TUnit, TVar id2)), JValue when id1 = id2 -> 
        (TUnit, JComp)
      | _ -> term_error "print_char expects a value of the form rec(t,unit +t)"
    end
  in aux []

(* DYNAMICS *)

let (let*) = Option.bind

(* [step t] returns (Some t') where t -> t' or None if evaluation is stuck *)
let rec step = function
  | Print_char e -> print_char_term e; Some (Return Unit)
  | Application (Abstraction (_, x, e1), e2) -> Some (substitute x e2 e1)
  | Bind (Return v, x, e2) -> Some (substitute x v e2)
  | Bind (e1, x, e2) -> let* e' = step e1 in Some (Bind (e', x, e2))
  | Force (Computation e) -> Some e
  | Case (Left (_, v), x, e, _, _) -> Some (substitute x v e)
  | Case (Right (_, v), _, _, x, e) -> Some (substitute x v e)
  | Case (e, x1, e1, x2, e2) ->
    let* e' = step e in Some(Case (e', x1, e1, x2, e2))
  | Split (Tuple (a, b), x1, x2, e) -> Some (substitute x1 a (substitute x2 b e))
  | Unfold (Fold ( _, e)) -> Some (Return e)
  | Unfold e -> let* e' = step e in Some(Unfold e')
  | _ -> None

let rec eval t =
  match step t with
  | Some t' -> eval t'
  | None -> t

open Format
open Parsing

let execute program quiet =
  let verbose = not quiet in
  let rec one tenv tyenv matenv matyenv seen = function
    | Type (n, t) ->
      if verbose then printf "type %s : %a@," n pp_ttype t;
      tenv, (n, t) :: tyenv, matenv, matyenv, seen
    | DeclareMacro (n, tparams, params, t) ->
      if verbose then printf "Macro %s registered@." n;
      tenv, tyenv, (n, tparams, params, t) :: matenv, matyenv, seen
    | Typemacro (n, params, t) ->
      if verbose then printf "Typemacro %s registered@." n;
      tenv, tyenv, matenv, (n, params, t) :: matyenv, seen
    | Declare (n, t) ->
      let ts = texpand_everything tenv tyenv matenv matyenv t in
      let tau, j = typecheck ts in
      if verbose then printf "%a %s : %a@." pp_judgement j n pp_ttype tau;
      if j = JValue then
        (n, ts) :: tenv, tyenv, matenv, matyenv, seen
      else begin match eval ts with
        | Return v -> (n, v) :: tenv, tyenv, matenv, matyenv, seen
        | stuck ->
          let msg = Format.asprintf
              "Declare %s got stuck before value or return. Left with @.%a"
              n pp_term stuck
          in failwith msg
      end
    | Check t ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      let r = typecheck t' in
      if verbose then printf "check -> %a@." pp_metatype r;
      tenv, tyenv, matenv, matyenv, seen
    | Eval t ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      let tau, j = typecheck t' in
      let r = eval t' in
      if verbose then printf "eval -> %a %a =@,%a@." pp_judgement j pp_ttype tau pp_term r;
      tenv, tyenv, matenv, matyenv, seen
    | Include n ->
      if List.mem n seen then tenv, tyenv, matenv, matyenv, seen
      else
        let replaced = String.map (fun c -> if c = '.' then '/' else c) n in
        aux tenv tyenv matenv matyenv (n :: seen) (parse (replaced ^ ".bob"))
  and aux tenv tyenv matenv matyenv seen = function
    | [] ->
      (tenv, tyenv, matenv, matyenv, seen)
    | h :: t ->
      let tenv', tyenv', matenv', matyenv', seen =
        one tenv tyenv matenv matyenv seen h in
      aux tenv' tyenv' matenv' matyenv' seen t
  in if verbose then printf "@[<v>";
  ignore (aux [] [] [] [] [] program);
  if verbose then printf "Done, bye!@,@]"

let main =
  let fn = Sys.argv.(1) in
  let quiet = Array.length Sys.argv > 2 && Sys.argv.(2) = "quiet" in
  let program = parse fn in
  execute program quiet
