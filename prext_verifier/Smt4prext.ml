open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector


type sym = string

type term=
| T_lit of int
| T_var of sym
| T_add of (term * term)
| T_sub of (term * term)
| T_mul of (term * term)

type formula = 
| F_eq of (term * term)
| F_lt of (term * term)
| F_and of (formula * formula)
| F_neg of (formula)


exception TestFailedException of string

let rec getZexprOfVar var varZexprList ctx=
  match varZexprList with
    [] -> let s_x = (mk_string ctx var) in
	let x = (Arithmetic.Integer.mk_const ctx s_x) in
	(x,(var,x)::varZexprList)
  | h::t -> let (v,e)=h in
	if v=var then (e,varZexprList)
	else getZexprOfVar var t ctx

let rec getZexprOfLit lit varZexprList ctx=
  (Arithmetic.Integer.mk_numeral_i ctx lit,varZexprList)

let rec getZexprOfTerm trm varZexprList ctx=
  match trm with
    T_lit i -> getZexprOfLit i varZexprList ctx
  | T_var v -> getZexprOfVar v varZexprList ctx
  | T_add (t1, t2) -> 
	let (e1,newlist)=getZexprOfTerm t1 varZexprList ctx in
	let (e2,newlist)=getZexprOfTerm t2 newlist ctx in
	(Arithmetic.mk_add ctx [e1; e2], newlist)
  | T_sub (t1, t2) -> 
	let (e1,newlist)=getZexprOfTerm t1 varZexprList ctx in
	let (e2,newlist)=getZexprOfTerm t2 newlist ctx in
	(Arithmetic.mk_sub ctx [e1; e2], newlist)
  | T_mul (t1, t2) -> 
	let (e1,newlist)=getZexprOfTerm t1 varZexprList ctx in
	let (e2,newlist)=getZexprOfTerm t2 newlist ctx in
	(Arithmetic.mk_mul ctx [e1; e2], newlist)

let rec make_assertion formula ctx varZexprList=
  match formula with
    F_eq(t1,t2) -> 
	let (e1,newlist)=getZexprOfTerm t1 varZexprList ctx in
	let (e2,newlist)=getZexprOfTerm t2 newlist ctx in
	(Boolean.mk_eq ctx e1 e2,newlist)
  | F_lt(t1,t2) -> 
	let (e1,newlist)=getZexprOfTerm t1 varZexprList ctx in
	let (e2,newlist)=getZexprOfTerm t2 newlist ctx in
	((Arithmetic.mk_lt ctx e1 e2),newlist)
  | F_and(f1,f2) -> 
	let (asr1,newlist)=make_assertion f1 ctx varZexprList in
	let (asr2,newlist)=make_assertion f2 ctx newlist in
	((Boolean.mk_and ctx [asr1;asr2]),newlist)
  | F_neg(f1) -> 
	let (asr1,newlist)=make_assertion f1 ctx varZexprList in
	((Boolean.mk_not ctx asr1),newlist)

let rec make_assertions1 formulas ctx varZexprList=
  match formulas with
    [] -> []
  | h::t -> let (assertion,newlist)=make_assertion h ctx varZexprList in
	assertion::(make_assertions1 t ctx newlist)

let satisfiable formulas=
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in
  let assertion_list=make_assertions1 formulas ctx [] in 
  let solver1 = (mk_solver ctx None) in
  (Solver.add solver1 assertion_list); 
  let q = (check solver1 []) in
  if q != SATISFIABLE then 
    false
  else
    true
