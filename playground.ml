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
  | TRecursive of identifier * ttype
  | TVar of identifier

let rec pp_ttype fmt = function
  | TUnit -> pp_print_string fmt "1"
  | TArrow (t1, t2) -> fprintf fmt "(%a -> %a)" pp_ttype t1 pp_ttype t2
  | TComp t -> fprintf fmt "comp(%a)" pp_ttype t
  | TSum (t1, t2) -> fprintf fmt "(%a + %a)" pp_ttype t1 pp_ttype t2
  | TProduct (t1, t2) -> fprintf fmt "(%a x %a)" pp_ttype t1 pp_ttype t2
  | TRecursive (id, t) -> fprintf fmt "rec(%s -> %a)" id pp_ttype t
  | TVar s -> pp_print_string fmt s

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
  | Left of ttype * term
  | Right of ttype * term
  | Case of term * identifier * term * identifier * term
  | Tuple of term * term
  | Split of term * identifier * identifier * term
  | Fold of ttype * term
  | Unfold of term

let rec pp_term fmt = function
  | Unit -> pp_print_string fmt "()"
  | Variable v -> pp_print_string fmt v
  | Computation t -> fprintf fmt "@[<hv 2>comp(@,%a@]@,)" pp_term t
  | Abstraction (_, id, e) -> fprintf fmt "@[<hv 2>λ(%s,@ %a@]@,)" id pp_term e
  | Return t -> fprintf fmt "ret (%a)" pp_term t
  | Bind (t, id, e) -> fprintf fmt "@[<hv 2>let %s =@ %a@]@ in %a" id pp_term t pp_term e
  | Application (t1, t2) -> fprintf fmt "@[<hv 2>(@,%a@ . %a@]@,)" pp_term t1 pp_term t2
  | Left (_, t) -> fprintf fmt "@[<hv 2>left(@,%a@]@,)"
                     pp_term t
  | Right (_, t) -> fprintf fmt "@[<hv 2>right(@,%a@]@,)"
                      pp_term t
  | Case (e, x1, e1, x2, e2) ->
    fprintf fmt "@[<hv 2>(match@ %a with@ left(%s) ->@ %a@ right(%s) ->@ %a@]@,)"
      pp_term e x1 pp_term e1 x2 pp_term e2
  | Tuple (t1, t2) -> fprintf fmt "@[<hv 2><%a,@ %a@]@,>" pp_term t1 pp_term t2
  | Split (e, x1, x2, e') ->
    fprintf fmt "@[<hv 2>(let <%s,%s> =@ %a@ in %a@]@,)"
      x1 x2 pp_term e pp_term e'
  | Fold (_, e) -> fprintf fmt "@[<hv 2>fold(@,%a@]@,)" pp_term e
  | Unfold e -> fprintf fmt "@[<hv 2>unfold(@,%a@]@,)" pp_term e

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
          else failwith "Incompatible types during application"
        else failwith "Functions only applicable to values"
      | _ -> failwith "Can only apply functional values"
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
  | Abstraction (tt, id, a) -> Abstraction (tt, id, substitute f t a)
  | Return r -> Return (substitute f t r)
  | Bind (t1, id, t2) -> Bind (substitute f t t1, id, substitute f t t2)
  | Application (t1, t2) -> Application (substitute f t t1, substitute f t t2)
  | Right (ty, e) -> Right (ty, substitute f t e)
  | Left (ty, e) -> Left (ty, substitute f t e)
  | Case (e, x1, e1, x2, e2) ->
    let e' = substitute f t e in
    let e1' = substitute f t e1 in
    let e2' = substitute f t e2 in
    Case (e', x1, e1', x2, e2')
  | Tuple (t1, t2) -> Tuple (substitute f t t1, substitute f t t2)
  | Split (e1, x1, x2, e2) ->
    let e1' = substitute f t e1 in
    let e2' = substitute f t e2 in
    Split (e1', x1, x2, e2')
  | Fold (a, e) -> Fold (a, substitute f t e)
  | Unfold e -> Unfold (substitute f t e)

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
let unroll e = 
  Bind (Computation (Unfold e), "tmp",
        Application (Variable "tmp", e)
       )

let fix tau x e =
  unroll (self tau "y" (substitute x (unroll (Variable "y")) e))


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

let double = fix int_t "double"
    (Abstraction (int_t, "x",
                  Bind (Computation (Unfold (Variable "x")), "x'",
                        Case (Variable "x'", "_", Return zero,
                              "e", Bind (Computation (Application (Variable "double",
                                                                   Variable "e")
                                                     ), "de",
                                         Return (succ (succ (Variable "de")))
                                        )
                             )
                       )
                 )
    )


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
  analyse_term applied;
  analyse_term two;
  analyse_term minus_one;
  analyse_term one;
  analyse_term double
