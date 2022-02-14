open Kernel
open Basic
open Rule
open Term
module SS = Exsubst.ExSubst

let d_typeChecking = Debug.register_flag "TypeChecking"

let d_rule = Debug.register_flag "Rule"

let coc = ref false

let fail_on_unsatisfiable_constraints = ref false

type typ = term

(* ********************** ERROR MESSAGES *)

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError of term * typed_context * term * term
  | AnnotConvertibilityError of loc * ident * typed_context * term * term
  | VariableNotFound of loc * ident * int * typed_context
  | SortExpected of term * typed_context * term
  | ProductExpected of term * typed_context * term
  | InexpectedKind of term * typed_context
  | DomainFreeLambda of loc
  | CannotInferTypeOfPattern of pattern * typed_context
  | UnsatisfiableConstraints of partially_typed_rule * (int * term * term)
  | BracketExprBoundVar of term * typed_context
  | BracketExpectedTypeBoundVar of term * typed_context * term
  | BracketExpectedTypeRightVar of term * typed_context * term
  | TypingCircularity of loc * ident * int * typed_context * term
  | FreeVariableDependsOnBoundVariable of
      loc * ident * int * typed_context * term
  | NotImplementedFeature of loc
  | Unconvertible of loc * term * term
  | Convertible of loc * term * term
  | Inhabit of loc * term * term

exception Typing_error of typing_error

let no_free_lam = 
  let rec aux = function
  | Kind | DB _ | Type _ | Const _ -> ()
  | App (f, a, al) -> 
    (aux f; aux a; List.iter aux al)
  | Lam (_,_,None,_) -> failwith "free lambda found"
  | Lam (_,_,Some ty,bd) -> (aux ty; aux bd)
  | Pi (_,_,a,b) -> (aux a; aux b)
  in
  aux

(* ********************** CONTEXT *)
module Make (R : Reduction.S) = struct
  module SR = Srcheck.SRChecker (R)

  let get_type ctx l x n =
    try
      let _, _, ty = List.nth ctx n in
      Subst.shift (n + 1) ty
    with Failure _ -> raise (Typing_error (VariableNotFound (l, x, n, ctx)))

  let extend_ctx a ctx = function
    | Type _ -> 
        let (_,_,te) = a in
        no_free_lam te;
        a :: ctx
    | Kind when !coc -> a :: ctx
    | ty_a ->
        let _, _, te = a in
        raise (Typing_error (ConvertibilityError (te, ctx, mk_Type dloc, ty_a)))

  (* ********************** TYPE CHECKING/INFERENCE FOR TERMS  *)

  (* The functions [check'] and [infer'] have an additional argument compared to [check] and [infer]
     which is a list of additional equalities, which are useful when checking subject reduction *)
  let rec infer' sg (c : SR.lhs_typing_cstr) (d : int) (ctx : typed_context)
  (te : term) : (term * typ) =
  Debug.(debug d_typeChecking "Inferring: %a" pp_term te);
  let check_res (te,ty) = (
    try no_free_lam te; no_free_lam ty; (te,ty)
    with e ->
      (Format.eprintf "\nNo free Lambda\n%a:%a\n\n%!" pp_term te pp_term ty; raise e)) in
  check_res @@ begin match te with
  | Kind                  -> raise (Typing_error KindIsNotTypable)
  | Type _                -> te, mk_Kind
  | DB (l, x, n)          -> te, get_type ctx l x n
  | Const (l, cst)        -> te, Signature.get_type sg l cst
  | App (f, a, args)      ->
    begin
      let (f',ty_f) = infer' sg c d ctx f in
      let ty_f' = (try fst @@ infer' sg c d ctx ty_f with Typing_error KindIsNotTypable -> ty_f) in
      let (acc,_,ty_af) = (List.(fold_left (check_app sg c d ctx) ([], f, ty_f') (a::args))) in
      match List.rev acc with
      | a' :: args' -> (mk_App f' a' args',ty_af)
      | _ -> failwith "not possible"
    end
      (* (te, snd
        (List.fold_left (check_app sg c d ctx)
          (f, snd @@ infer' sg c d ctx f)
          (a :: args))) *)
  | Pi (l, x, a, b)       -> (
      let (a,ty_a) = infer' sg c d ctx a in
      let ty_a = (try fst @@ infer' sg c d ctx ty_a with Typing_error KindIsNotTypable -> ty_a) in
      let ctx2 = extend_ctx (l, x, a) ctx ty_a in
      let (b,ty_b) = infer' sg c (d + 1) ctx2 b in
      let ty_b = (try fst @@ infer' sg c (d+1) ctx2 ty_b with Typing_error KindIsNotTypable -> ty_b) in
      match ty_b with
      | Kind | Type _ -> (mk_Pi l x a b, ty_b)
      | _             -> raise (Typing_error (SortExpected (b, ctx2, ty_b))))
  | Lam (l, x, Some a, b) -> (
      let (a,ty_a) = infer' sg c d ctx a in
      let ty_a = (try fst @@ infer' sg c d ctx ty_a with Typing_error KindIsNotTypable -> ty_a) in
      let ctx2 = extend_ctx (l, x, a) ctx ty_a in
      let (b,ty_b) = infer' sg c (d + 1) ctx2 b in
      let ty_b = (try fst @@ infer' sg c (d+1) ctx2 ty_b with Typing_error KindIsNotTypable -> ty_b) in
      match ty_b with
      | Kind -> raise (Typing_error (InexpectedKind (b, ctx2)))
      | _    -> (mk_Lam l x (Some a) b, mk_Pi l x a ty_b))
  | Lam (l, _, None, _)   -> 
      Format.eprintf "Domain free Lambda: %a\n" Term.pp_term te;
      raise (Typing_error (DomainFreeLambda l))
  end

  and check' sg (c : SR.lhs_typing_cstr) (d : int) (ctx : typed_context)
    (te : term) (ty_exp : typ) : term =
  Debug.debug d_typeChecking "Checking (%a) [%a]: %a : %a" pp_loc (get_loc te)
    pp_typed_context ctx pp_term te pp_term ty_exp;
  let te = begin match te with
  | Lam (l, x, op, b) -> (
      match R.whnf sg ty_exp with
      | Pi (_, _, a, ty_b) ->
          (match op with
          | Some a' ->
              ignore (infer' sg c d ctx a');
              Debug.(debug d_typeChecking 
                "Checking convertibility: %a ~ %a" 
                pp_term a pp_term a');
              (* Format.printf "Checking convertiblility:\n\t%a ~~~ %a\n\n"
                pp_term a pp_term a'; *)
              if not (SR.convertible sg c d a a') then
                raise
                  (Typing_error
                    (ConvertibilityError (mk_DB l x 0, ctx, a, a')))
          | _       -> ());
          mk_Lam l x (Some a) (check' sg c (d + 1) ((l, x, a) :: ctx) b ty_b)
      | _                  -> raise
                                (Typing_error
                                  (ProductExpected (te, ctx, ty_exp))))
  | _                 ->
    begin
      let (te,ty_inf) = infer' sg c d ctx te in
      Debug.(
        debug d_typeChecking "Checking convertibility: %a ~ %a" pp_term ty_inf
          pp_term ty_exp);
      (if not (SR.convertible sg c d ty_inf ty_exp) then
        let ty_exp' = rename_vars_with_typed_context ctx ty_exp in
        raise (Typing_error (ConvertibilityError (te, ctx, ty_exp', ty_inf))));
      te
    end
  end in
  no_free_lam te; te

  and check_app sg (c : SR.lhs_typing_cstr) (d : int) (ctx : typed_context)
    ((acc ,f, ty_f) : (term List.t) * term * typ) (arg : term) : (term List.t) * term * typ =
  Debug.(debug d_typeChecking "Reducing %a" pp_term ty_f);
  let t = R.whnf sg ty_f in
  Debug.(debug d_typeChecking "Reduced %a" pp_term t);
  match t with
  | Pi (_, _, a, b) ->
      let arg' = check' sg c d ctx arg a in
      let app = mk_App f arg' [] in
      let tl = Subst.subst b arg' in
      no_free_lam arg'; 
      no_free_lam app; 
      no_free_lam tl;
      (arg'::acc, app, tl)
  | _               -> raise (Typing_error (ProductExpected (f, ctx, ty_f)))

  let check sg ctx te ty = check' sg SR.empty 0 ctx te ty

  let infer sg ctx ty = infer' sg SR.empty 0 ctx ty

  let inference sg (te : term) : term * typ = infer sg [] te

  let checking sg (te : term) (ty : term) : term =
  let _ = infer sg [] ty in
  check sg [] te ty
end

module Default = Make (Reduction.Default)
