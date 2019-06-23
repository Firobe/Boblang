type identifier = string
[@@deriving show]

open Format

type judgement =
  | JValue
  | JComp
[@@deriving show {with_path = false}]

type ttype =
  | TUnit
  | TArrow of ttype * ttype
  | TComp of ttype
  | TSum of ttype * ttype
  | TProduct of ttype * ttype

let rec pp_ttype fmt = function
  | TUnit -> pp_print_string fmt "1"
  | TArrow (t1, t2) -> fprintf fmt "(%a -> %a)" pp_ttype t1 pp_ttype t2
  | TComp t -> fprintf fmt "comp(%a)" pp_ttype t
  | TSum (t1, t2) -> fprintf fmt "(%a + %a)" pp_ttype t1 pp_ttype t2
  | TProduct (t1, t2) -> fprintf fmt "(%a x %a)" pp_ttype t1 pp_ttype t2

type metatype = ttype * judgement
[@@deriving show {with_path=false}]

type term =
  | Unit
  | Variable of identifier
  | Computation of term
  | Abstraction of ttype * identifier * term
  | Return of term
  | Bind of term * identifier * term
  | Application of term * term
  | Left of ttype * ttype * term
  | Right of ttype * ttype * term
  | Case of term * identifier * term * identifier * term
  | Tuple of term * term
  | Split of term * identifier * identifier * term

let rec pp_term fmt = function
  | Unit -> pp_print_string fmt "()"
  | Variable v -> pp_print_string fmt v
  | Computation t -> fprintf fmt "@[<hv 2>comp(@,%a@]@,)" pp_term t
  | Abstraction (_, id, e) -> fprintf fmt "@[<hv 2>λ(%s,@ %a@]@,)" id pp_term e
  | Return t -> fprintf fmt "ret (%a)" pp_term t
  | Bind (t, id, e) -> fprintf fmt "@[<hv 2>let %s =@ %a@]@ in %a" id pp_term t pp_term e
  | Application (t1, t2) -> fprintf fmt "@[<hv 2>(@,%a@ . %a@]@,)" pp_term t1 pp_term t2
  | Left (tau1, tau2, t) -> fprintf fmt "@[<hv 2>left[%a + %a](@,%a@]@,)"
                              pp_ttype tau1 pp_ttype tau2 pp_term t
  | Right (tau1, tau2, t) -> fprintf fmt "@[<hv 2>right[%a + %a](@,%a@]@,)"
                              pp_ttype tau1 pp_ttype tau2 pp_term t
  | Case (e, x1, e1, x2, e2) ->
    fprintf fmt "@[<hv 2>(match@ %a with@ left(%s) ->@ %a@ right(%s) ->@ %a@]@,)"
      pp_term e x1 pp_term e1 x2 pp_term e2
  | Tuple (t1, t2) -> fprintf fmt "@[<hv 2><%a,@ %a@]@,>" pp_term t1 pp_term t2
  | Split (e, x1, x2, e') ->
    fprintf fmt "@[<hv 2>(let <%s,%s> =@ %a@ in %a@]@,)"
      x1 x2 pp_term e pp_term e'

(* Statics *)

let typecheck =
  let rec aux env = function
  | Unit -> (TUnit, JValue)
  | Variable v ->
    begin match List.assoc_opt v env with
      | None -> failwith "NIIIII"
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
          else failwith "Incompatible types during application"
        else failwith "Functions only applicable to values"
      | _ -> failwith "Can only apply functions"
    end
  | Left (tau1, tau2, e) ->
    let tau'', j = aux env e in
    if j = JValue then
      if tau'' = tau1 then (TSum (tau1, tau2), JValue)
      else failwith "Wrong annotation in left"
    else failwith "Left expects a value"
  | Right (tau1, tau2, e) ->
    let tau'', j = aux env e in
    if j = JValue then
      if tau'' = tau2 then (TSum (tau1, tau2), JValue)
      else failwith "Wrong annotation in right"
    else failwith "Right expects a value"
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
  in aux []

(* Dynamics *)

let opb o f = match o with
  | None -> None
  | Some x -> Some (f x)

let nid = ref 0
let new_name () =
  nid := 1 + !nid;
  "v" ^ (string_of_int !nid)

let rec new_name_not id =
  let nn = new_name () in
  if nn = id then new_name_not id else nn

(* [substitute f t e] replaces variables named f in e by term t] *)
let rec substitute f t = function
  | Unit -> Unit
  | Variable v when v = f -> t
  | Variable v -> Variable v
  | Computation c -> Computation (substitute f t c)
  | Abstraction (tt, id, a) when id = f ->
    let nn = new_name () in
    let beta = substitute id (Variable nn) a in
    substitute f t (Abstraction (tt, nn, beta))
  | Abstraction (tt, id, a) -> Abstraction (tt, id, substitute f t a)
  | Return r -> Return (substitute f t r)
  | Bind (t1, id, t2) when id = f ->
    let nn = new_name () in
    let beta = substitute id (Variable nn) t2 in
    substitute f t (Bind (t1, nn, beta))
  | Bind (t1, id, t2) -> Bind (substitute f t t1, id, substitute f t t2)
  | Application (t1, t2) -> Application (substitute f t t1, substitute f t t2)
  | Right (t1, t2, e) -> Right (t1, t2, substitute f t e)
  | Left (t1, t2, e) -> Left (t1, t2, substitute f t e)
  | Case (e, x1, e1, x2, e2) when f = x1 ->
    let nn = new_name_not f in
    let e1' = substitute x1 (Variable "nn") e1 in
    substitute f t (Case (e, nn, e1', x2, e2))
  | Case (e, x1, e1, x2, e2) when f = x2 ->
    let nn = new_name_not f in
    let e2' = substitute x2 (Variable "nn") e2 in
    substitute f t (Case (e, x1, e1, nn, e2'))
  | Case (e, x1, e1, x2, e2) ->
    let e' = substitute f t e in
    let e1' = substitute f t e1 in
    let e2' = substitute f t e2 in
    Case (e', x1, e1', x2, e2')

(* [step t] returns (Some t') where t -> t' or None if evaluation is stuck *)
let rec step = function
  | Application (Abstraction (_, x, e1), e2) -> Some (substitute x e2 e1)
  | Bind (Computation (Return v), x, e) -> Some (substitute x v e)
  | Bind (Computation e, x, e2) ->
    opb (step e) (fun e' -> Bind (Computation e', x, e2))
  | Case (Left (_, _, v), x, e, _, _) -> Some (substitute x v e)
  | Case (Right (_, _, v), _, _, x, e) -> Some (substitute x v e)
  | Case (e, x1, e1, x2, e2) ->
    opb (step e) (fun e' -> Case (e', x1, e1, x2, e2))
  | _ -> None

(* Testing *)

let bool_t = TSum (TUnit, TUnit)
let btrue = Left (TUnit, TUnit, Unit)
let bfalse = Right (TUnit, TUnit, Unit)

let double = Abstraction(TArrow (bool_t, bool_t), "f",
                Return (Abstraction(bool_t, "x",
                    Bind(
                        Computation (Application (Variable "f", Variable "x")),
                        "tmp", Application (Variable "f", Variable "tmp")))))

let identity = Abstraction(bool_t, "x", Return (Variable "x"))
let flip = Abstraction(bool_t, "b",
            Case(Variable "b", "true", Return bfalse, "false", Return btrue))

let twiceid = Abstraction (bool_t, "x",
                Bind (Computation(Application (double, flip)), "res",
                      Application (Variable "res", Variable "x")))

let applied = Application (twiceid, btrue)

let rec eval t =
  Format.printf "@,===================================@,@[<hv>%a@]" pp_term t;
  match step t with
  | Some t' -> eval t'
  | None -> t

let analyse_term todo =
  printf "@[<v>@,~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~";
  ignore @@ eval todo;
  printf "@,Evaluation stuck!@,@]";
  let t = typecheck todo in
  printf "--> Type: %a@," pp_metatype t

let _ =
  analyse_term double;
  analyse_term identity;
  analyse_term twiceid;
  analyse_term applied
