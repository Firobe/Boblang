open Utils

(* STATICS *)

let typecheck =
  let rec aux env = function
  | Unit -> (TUnit, JValue)
  | Variable v ->
    begin match List.assoc_opt v env with
      | None -> failwith ("Variable " ^ v ^ " is not bound")
      | Some t -> (t, JValue)
    end
  | Computation t ->
    let tau, j = aux env t in
    if j = JComp then (TComp tau, JValue)
    else failwith "comp() expects a computation"
  | Abstraction (tau, id, t) ->
    let tau', j = aux ((id, tau) :: env) t in
    if j = JComp then (TArrow (tau, tau'), JValue)
    else failwith "Abstractions should return computations"
  | Return t ->
    let tau, j = aux env t in
    if j = JValue then (tau, JComp)
    else failwith "Only values can be returned"
  | Bind (e1, id, e2) ->
    begin match aux env e1 with
      | TComp tau, JValue ->
        let tau', j' = aux ((id, tau) :: env) e2 in
        if j' = JComp then (tau', JComp)
        else failwith "Bind should return a computation"
      | _ -> failwith "Bind should be on a comp()"
    end
  | Application (e1, e2) ->
    begin match aux env e1 with
      | TArrow (tau, tau'), JValue ->
        let tau'', j = aux env e2 in
        if j = JValue then
          if tau'' = tau then (tau', JComp)
          else (
            Format.printf "%a ; %a@," pp_ttype tau'' pp_ttype tau;
            failwith "Incompatible types during application"
          )
        else failwith "Functions only applicable to values"
      | tt -> Format.printf "%a : %a" pp_term e1 pp_metatype tt;
        failwith "Can only apply functional values"
    end
  | Left (TSum (tau1, tau2), e) ->
    let tau'', j = aux env e in
    if j = JValue then
      if tau'' = tau1 then (TSum (tau1, tau2), JValue)
      else failwith "Wrong annotation in left"
    else failwith "Left expects a value"
  | Left _ -> failwith "Left expects a sum type annotation"
  | Right (TSum (tau1, tau2), e) ->
    let tau'', j = aux env e in
    if j = JValue then
      if tau'' = tau2 then (TSum (tau1, tau2), JValue)
      else failwith "Wrong annotation in right"
    else failwith "Right expects a value"
  | Right _ -> failwith "Right expects a sum type annotation"
  | Case (e, x1, e1, x2, e2) ->
    begin match aux env e with
      | TSum (tau1, tau2), JValue ->
        let tau, j' = aux ((x1, tau1) :: env) e1 in
        let tau', j'' = aux ((x2, tau2) :: env) e2 in
        if tau = tau' then
          if j' = JComp then
            if j'' = JComp then (tau, JComp)
            else failwith "Second branch of case is not a comput"
          else failwith "First branch of case is not a comput"
        else failwith "Branches in case do not have the same type"
      | _ -> failwith "Case expects a value of type sum"
    end
  | Tuple (v1, v2) ->
    let tau1, j1 = aux env v1 in
    let tau2, j2 = aux env v2 in
    if j1 = JValue then
      if j2 = JValue then (TProduct (tau1, tau2), JValue)
      else failwith "Second component of tuple must be a value"
    else failwith "First component of tuple must be a value"
  | Split (e, x1, x2, e') ->
    begin match aux env e with
      | TProduct (tau1, tau2), JValue ->
        let tau, j = aux ((x1, tau1) :: (x2, tau2) :: env) e' in
        if j = JComp then (tau, JComp)
        else failwith "Result of split should a computation"
      | _ -> failwith "Split expects a value of type product"
    end
  | Unfold e ->
    begin match aux env e with
      | TRecursive (id, tau) as rect, JValue ->
        tsubstitute id rect tau, JComp
      | _ -> failwith "Unfold expects a recursive value"
    end
  | Fold (TRecursive(id, tau), e) ->
    let rect = TRecursive (id, tau) in
    let tau', j = aux env e in
    if j = JValue then
      if tau' = tsubstitute id rect tau
      then rect, JValue
      else failwith "Good luck with that"
    else failwith "Fold expects a value"
  | Fold _ -> failwith "Fold expect a recursive type annotation"
  | Macro (n, _, _) -> failwith ("Macro " ^ n ^ " not expanded")
  in aux []

(* DYNAMICS *)

let opb o f = match o with
  | None -> None
  | Some x -> Some (f x)

(* [step t] returns (Some t') where t -> t' or None if evaluation is stuck *)
let rec step = function
  | Application (Abstraction (_, x, e1), e2) -> Some (substitute x e2 e1)
  | Bind (Computation (Return v), x, e) -> Some (substitute x v e)
  | Bind (Computation e, x, e2) ->
    opb (step e) (fun e' -> Bind (Computation e', x, e2))
  | Case (Left (_, v), x, e, _, _) -> Some (substitute x v e)
  | Case (Right (_, v), _, _, x, e) -> Some (substitute x v e)
  | Case (e, x1, e1, x2, e2) ->
    opb (step e) (fun e' -> Case (e', x1, e1, x2, e2))
  | Split (Tuple (a, b), x1, x2, e) -> Some (substitute x1 a (substitute x2 b e))
  | Unfold (Fold ( _, e)) -> Some (Return e)
  | Unfold e -> opb (step e) (fun e' -> Unfold e')
  | _ -> None

let rec eval t =
  match step t with
  | Some t' -> eval t'
  | None -> t

open Format
open Parsing

let execute =
  let one tenv tyenv matenv matyenv = function
    | Declare (n, t) ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      let ts = texpand_everything tenv tyenv (("SUBSTITUTE", [], [], Unit) ::
                                              matenv) matyenv t' in
      let tau, j = typecheck ts in
      printf "%a %s : %a@," pp_judgement j n pp_ttype tau;
      (n, ts) :: tenv, tyenv, matenv, matyenv
    | Type (n, t) ->
      let t' = tyexpand_everything tyenv matyenv t in
      printf "type %s : %a@," n pp_ttype t';
      tenv, (n, t') :: tyenv, matenv, matyenv
    | DeclareMacro (n, tparams, params, t) ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      printf "Macro %s registered@," n;
      tenv, tyenv, (n, tparams, params, t') :: matenv, matyenv
    | Typemacro (n, params, t) ->
      let t' = tyexpand_everything tyenv matyenv t in
      printf "Typemacro %s registered@," n;
      tenv, tyenv, matenv, (n, params, t') :: matyenv
    | Check t ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      let r = typecheck t' in
      printf "check -> %a@," pp_metatype r;
      tenv, tyenv, matenv, matyenv
    | Eval t ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      let tau, j = typecheck t' in
      let r = eval t' in
      printf "eval -> %a %a =@,%a@," pp_judgement j pp_ttype tau pp_term r;
      tenv, tyenv, matenv, matyenv
  in
  let rec aux tenv tyenv matenv matyenv = function
    | [] -> printf "Done, bye!@,@]"
    | h :: t ->
      let tenv', tyenv', matenv', matyenv' = one tenv tyenv matenv matyenv h in
      printf "@,";
      aux tenv' tyenv' matenv' matyenv' t
  in 
  printf "@[<v>";
  aux [] [] [] []

let main =
  let fn = Sys.argv.(1) in
  let program = parse fn in
  execute program
