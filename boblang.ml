open Utils

(* STATICS *)

let rec tsubstitute f t = function
  | TUnit -> TUnit
  | TVar id when id = f -> t
  | (TVar _) as v -> v
  | TArrow (tau1, tau2) -> 
    TArrow (tsubstitute f t tau1, tsubstitute f t tau2)
  | TComp tau -> TComp (tsubstitute f t tau)
  | TSum (tau1, tau2) -> TSum (tsubstitute f t tau1, tsubstitute f t tau2)
  | TProduct (tau1, tau2) -> TProduct (tsubstitute f t tau1, tsubstitute f t tau2)
  | (TRecursive (id, _)) as r when id = f -> r
  | TRecursive (id, tau) -> TRecursive (id, tsubstitute f t tau)
  | TMacro (id, tl) -> TMacro (id, List.map (tsubstitute f t) tl)

let typecheck =
  let rec aux env = function
  | Unit -> (TUnit, JValue)
  | Variable v ->
    begin match List.assoc_opt v env with
      | None -> failwith "Some variable is not bound"
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
  | Macro _ -> assert false
  in aux []

(* DYNAMICS *)

let opb o f = match o with
  | None -> None
  | Some x -> Some (f x)

(* [substitute f t e] replaces variables named f in e by term t] *)
let rec substitute f t = function
  | Unit -> Unit
  | Variable v when v = f -> t
  | Variable v -> Variable v
  | Computation c -> Computation (substitute f t c)
  | Abstraction (_, id, _) as whole when id = f -> whole
  | Abstraction (tt, id, a) -> Abstraction (tt, id, substitute f t a)
  | Return r -> Return (substitute f t r)
  | Bind (t1, id, t2) ->
    Bind (substitute f t t1, id, if id = f then t2 else substitute f t t2)
  | Application (t1, t2) -> Application (substitute f t t1, substitute f t t2)
  | Right (ty, e) -> Right (ty, substitute f t e)
  | Left (ty, e) -> Left (ty, substitute f t e)
  | Case (e, x1, e1, x2, e2) ->
    let e' = substitute f t e in
    let e1' = if f = x1 then e1 else substitute f t e1 in
    let e2' = if f = x2 then e2 else substitute f t e2 in
    Case (e', x1, e1', x2, e2')
  | Tuple (t1, t2) -> Tuple (substitute f t t1, substitute f t t2)
  | Split (e1, x1, x2, e2) ->
    let e1' = substitute f t e1 in
    let e2' = if f = x1 || f = x2 then e2 else substitute f t e2 in
    Split (e1', x1, x2, e2')
  | Fold (a, e) -> Fold (a, substitute f t e)
  | Unfold e -> Unfold (substitute f t e)
  | Macro (id, tl) -> Macro (id, List.map (substitute f t) tl)

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

(* Self-reference definitions *)

let self_t tau = TRecursive("t", TArrow (TVar "t", tau))
let self tau x e = Fold (self_t tau,
                Abstraction(self_t tau, x, e))

let name_id = ref 0
let new_name () =
  name_id := !name_id + 1;
  "_" ^ (string_of_int !name_id)

let unroll e = 
  let nn = new_name () in
  Bind (Computation (Unfold e), nn,
        Application (Variable nn, e)
       )

let fix tau x e =
  let nn = new_name () in
  unroll (self tau nn (substitute x (unroll (Variable nn)) e))

(* TESTING *)

(* Basic PCF *)

let bool_t = TSum (TUnit, TUnit)
let btrue = Left (bool_t, Unit)
let bfalse = Right (bool_t, Unit)

let double_b = Abstraction(TArrow (bool_t, bool_t), "f",
                Return (Abstraction(bool_t, "x",
                    Bind(
                        Computation (Application (Variable "f", Variable "x")),
                        "tmp", Application (Variable "f", Variable "tmp")))))

let identity = Abstraction(bool_t, "x", Return (Variable "x"))
let flip = Abstraction(bool_t, "b",
            Case(Variable "b", "true", Return bfalse, "false", Return btrue))

let twiceid = Abstraction (bool_t, "x",
                Bind (Computation(Application (double_b, flip)), "res",
                      Application (Variable "res", Variable "x")))

let applied = Application (twiceid, btrue)

(* Recursive type, finite algorithms *)

(* Int = Unit + Int *)
let int_t = TRecursive ("t", TSum (TUnit, TVar "t"))
let zero = Fold(int_t, Left (TSum (TUnit, int_t), Unit))
let succ e = Fold(int_t, Right (TSum (TUnit, int_t), e))

let two = succ (succ zero)

let minus_one = Abstraction (int_t, "i",
                   Bind(Computation(Unfold (Variable "i")), "x",
                      Case(Variable "x", "zero", Return (Variable "i"),
                           "pred", Return (Variable "pred"))))

let one = Application (minus_one, two)

(* Recursive function on recursive data structure *)

let selft = self TUnit "id" (Return Unit)
let unrollt = unroll selft
let infinite = fix (TArrow (TUnit, TUnit)) "infinite"
    (Return 
       (Abstraction (TUnit, "_",
                     Bind (Computation (Variable "infinite"),
                           "rec", Application (Variable "rec", Unit)
                          )
                    )
       )
    )

(* Takes an integer an doubles it *)
let double = fix (TArrow (int_t, int_t)) "double"
    (Return 
       (Abstraction (int_t, "x",
                     Bind (Computation (Unfold (Variable "x")), "x'",
                           Case (Variable "x'", "_", Return zero,
                                 "e", 
                                 Bind (Computation (Variable "double"), "rec",
                                       Bind (Computation (Application (Variable "rec",
                                                                       Variable "e")
                                                         ), "de",
                                             Return (succ (succ (Variable "de")))
                                            )
                                      )
                                )
                          )
                    )
       )
    )

let five = succ (succ (succ (succ (succ zero))))
(* Should return ten *)
let apply_double =
  Bind (Computation double, "f", Application (Variable "f", five))


let rec eval t =
  match step t with
  | Some t' -> eval t'
  | None -> t

open Format

let analyse_term todo =
  printf "@[<v>@,~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~";
  ignore @@ eval todo;
  printf "@,Evaluation stuck!@,@]";
  let t = typecheck todo in
  printf "--> Type: %a@," pp_metatype t

let expand_known_types t =
  List.fold_left (fun e (id, v) -> tsubstitute id v e) t

let tyexpand_everything tyenv _ t =
  expand_known_types t tyenv

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
  | Bind (e1, id, e2) -> Bind (aux e1, id, aux e2)
  | Application (e1, e2) -> Application (aux e1, aux e2)
  | Left (t, e) -> Left (te t, aux e)
  | Right (t, e) -> Right (te t, aux e)
  | Case (e, x1, e1, x2, e2) -> Case (aux e, x1, aux e1, x2, aux e2)
  | Tuple (e1, e2) -> Tuple (aux e1, aux e2)
  | Split (e, x1, x2, e') -> Split (aux e, x1, x2, aux e')
  | Fold (t, e) -> Fold (te t, aux e)
  | Unfold t -> Unfold (aux t)
  | Macro (id, tl) -> Macro (id, List.map aux tl)
  in aux


let texpand_everything tenv tyenv _ matyenv t =
  let t' = expand_known_terms t tenv in
  expand_types_in_term tyenv matyenv t'

let execute =
  let one tenv tyenv matenv matyenv = function
    | Declare (n, t) ->
      let t' = texpand_everything tenv tyenv matenv matyenv t in
      let tau, j = typecheck t' in
      printf "%a %s : %a@," pp_judgement j n pp_ttype tau;
      (n, t') :: tenv, tyenv, matenv, matyenv
    | Type (n, t) ->
      let t' = tyexpand_everything tyenv matyenv t in
      printf "type %s : %a@," n pp_ttype t';
      tenv, (n, t') :: tyenv, matenv, matyenv
    | DeclareMacro _ -> assert false
    | Typemacro _ -> assert false
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

let print_position fmt lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  fprintf fmt "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse fn =
  let inx = open_in fn in
  let lexbuf = Lexing.from_channel inx in
  let res = try Bobgram.program Boblex.read lexbuf
    with Bobgram.Error -> 
      printf "%a: syntax error\n" print_position lexbuf;
      exit (-1)
  in close_in inx; res

let main =
  let fn = Sys.argv.(1) in
  let program = parse fn in
  execute program
