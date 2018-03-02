open Parser4prext;;
open Smt4prext;;

(*
==============================
PARSE INPUT
==============================
*)

let read_file filename = 
let lines = ref [] in
let chan = open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines ;;

let source = read_file "source.txt"

let routines = parse_program (String.concat "\n" source)

(*
==============================
STATE OUTCOME
==============================
*)

type pcond =
  Pcond of (formula list)

type chunks = 
  Chunks of (term * string)

type sstate =
  SState of (pcond * (var -> term) * (string -> term))

type ('s, 'a) outcome=
| Single of ('s * 'a)
| Demonic of (('s, 'a)outcome list)
| Angelic of (('s, 'a)outcome list)

let fork op1 op2=
  (fun sstate ->
     Demonic ([op1 sstate;op2 sstate])
  )

let ofail=
  Angelic ([])

let oblock=
  Demonic ([])

type unit=
  Unit

type 'a option=
| Some of ('a)
| None 

(*
==============================
SEQ COMPOSITION
==============================
*)

let rec map os bf f=
  match os with
    [] -> []
  | h::t -> (bf h f)::map t bf f

let rec bindf o f=
  match o with
    Single(sstate,a) -> f a sstate
  | Angelic (os) -> Angelic (map os bindf f) 
  | Demonic (os) -> Demonic (map os bindf f) 

let bind o c=
  bindf o (fun _ -> c)

let seqf c f=
  fun st -> bindf (c st) f

let seq c c'=
  seqf c (fun _ -> c')

let (@>) x y = seq x y 
;;

let yield x=
  fun (SState sstate) ->
	Single(SState sstate,x)
  
let seqcomma c c'=
  seqf (c)
       (fun x -> 
	       (c') @>
	       (yield x)
       )

let block_mut=
  (fun (SState sstate) ->
      Demonic([])
  )

let fail_mut=
  (fun (SState sstate) ->
      Angelic([])
  )

(*
==============================
FRESH SYMBOL
==============================
*)

let rec remove_duplicate_items lst=
  match lst with
    [] -> []
  | h::t -> if List.mem h t then remove_duplicate_items t
	else h::(remove_duplicate_items t)

let rec union1 l1 l2 =
    match l1 with
    | [] -> l2
    | h::t -> if (List.mem h l2) then (union1 t l2) else (union1 t (h::l2))

let rec union l1 l2 =
    remove_duplicate_items (union1 l1 l2)

let get_new_sym1 symbols=
  let rec strings2chars lstr=(
    match lstr with
      [] -> []
    | h::t -> (String.get h 0)::(strings2chars t)
  ) in
  let chars=strings2chars symbols in
  let rec find_max_sym char=(
    match char with 
      [] -> ((Char.code 'A')-1)
    | h::t -> max (Char.code h)(find_max_sym t)
  ) in
  Char.escaped (Char.chr ((find_max_sym chars)+1))

let rec get_syms_in_term trm=
  match trm with
    T_lit i -> []
  | T_var v -> [v] 
  | T_add(t1, t2) -> union (get_syms_in_term t1)(get_syms_in_term t2)
  | T_sub(t1, t2) -> union (get_syms_in_term t1)(get_syms_in_term t2)
  | T_mul(t1, t2) -> union (get_syms_in_term t1)(get_syms_in_term t2)

let rec get_syms_in_formula f=
  match f with 
    F_eq (t1, t2) -> union (get_syms_in_term t1)(get_syms_in_term t1)
  | F_lt (t1, t2) -> union (get_syms_in_term t1)(get_syms_in_term t1)
  | F_and (f1, f2) -> union (get_syms_in_formula f1)(get_syms_in_formula f1)
  | F_neg (f) -> get_syms_in_formula f

let rec get_syms_in_pcond pcond=
  match pcond with 
    [] -> []
  | h::t -> union (get_syms_in_formula h) (get_syms_in_pcond t)

let get_new_sym pcond=
  get_new_sym1 (get_syms_in_pcond pcond)

let fresh_mut=
  (fun (SState sstate) ->
    let (Pcond pcond,sstore,h)=sstate in
    let newsym=get_new_sym pcond in
    Single(SState sstate,T_var newsym)
  )

let fresh_muts varlist=
  (fun (SState sstate) ->
    let (Pcond pcond,sstore,h)=sstate in
    let syms=get_syms_in_pcond pcond in
    let rec produce_new_symbols syms varlist=(
      match varlist with
        [] -> []
      | h::t -> let new_sym= get_new_sym1 syms in
		let new_trm=T_var new_sym in
		(new_trm::produce_new_symbols (new_sym::syms) t)
    ) in
    let fresh_syms=produce_new_symbols syms varlist in
    Single(SState sstate,fresh_syms)
  )


(*
==============================
TO DEBUG
==============================
*)

let rec printTerm (t:term)=
  match t with
| T_lit i -> Printf.printf "%d" i
| T_var s -> Printf.printf "%s" s
| T_add (t1, t2) -> Printf.printf "("; printTerm t1; Printf.printf " + "; printTerm t2; Printf.printf ")"
| T_sub (t1, t2) -> Printf.printf "("; printTerm t1; Printf.printf " - "; printTerm t2; Printf.printf ")"
| T_mul (t1, t2) -> Printf.printf "("; printTerm t1; Printf.printf " * "; printTerm t2; Printf.printf ")"

let rec printFormula (f:formula)=
  match f with
| F_eq (t1, t2) -> printTerm t1; Printf.printf " == "; printTerm t2
| F_lt (t1, t2) -> printTerm t1; Printf.printf " < "; printTerm t2
| F_and (f1, f2) -> printFormula f1; Printf.printf " & "; printFormula f2
| F_neg f -> Printf.printf " ! "; printFormula f

let rec printFormulae fs=
  match fs with
    [] -> Printf.printf "\n"
   | h::t -> printFormula h; Printf.printf "  ##  "; printFormulae t


(*
==============================
AUXILIARY FUNCTIONS
==============================
*)

let rec seval s e=
  match e with
	| E_lit i -> T_lit i
	| E_var v -> s v
	| E_add (e1,e2) -> T_add (seval s e1,seval s e2)
	| E_sub (e1,e2) -> T_sub (seval s e1,seval s e2)
	| E_mul (e1,e2) -> T_mul (seval s e1,seval s e2)

let rec sevals s es=
  match es with 
    [] -> []
  | h::t -> (seval s h)::(sevals s t) 

let rec sbeval s b=
  match b with
    B_eq (e1, e2) -> F_eq ((seval s e1), (seval s e2))
  | B_lt (e1, e2) -> F_lt ((seval s e1), (seval s e2))
  | B_not b -> F_neg (sbeval s b)
  | B_and (b1, b2) -> F_and ((sbeval s b1),(sbeval s b2))

let sassume0 b=
  (fun (SState sstate) ->
    let (Pcond pcond,sstore,h)=sstate in
    let bformula=sbeval sstore b in
    let formulas=bformula::pcond in
    if satisfiable formulas=true then 
      Single(SState (Pcond (bformula::pcond),sstore,h),Unit)
    else
        oblock
  )

let sassert b=
  (fun (SState sstate) ->
    let (Pcond pcond,sstore,h)=sstate in
    let bformula=sbeval sstore b in
    let formulas=(F_neg bformula)::pcond in
    if satisfiable formulas=true then (
	printFormulae formulas;
       ofail
    )
    else
       Single(SState sstate,Unit)
  )

let rec printList l=
  match l with
    [] -> Printf.printf"\n"
  | h::t -> Printf.printf "%s, " h; printList t
(*
==============================
HEAP
==============================
*)

let seval_mut0 e=
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
	let a=seval sstore e in
	Single(SState (pcond,sstore,h),a)
  )


let sheap_add sheap chunk trm =
  (fun chnk ->
     if chnk=chunk then T_add(sheap chnk, trm)
	 else sheap chnk
  )

let sproduce_chunks(c: chunks)=
  (fun (SState sstate) ->
    let (pcond,sstore,sheap)=sstate in
    let Chunks(count, name)=c in
	Single(SState (pcond,sstore,sheap_add sheap name count),Unit)
  )

let rec sproduce a=
  match a with
    BAsn b -> sassume0 b 
  | AndAsn(a1, a2) -> (sproduce a1) @> (sproduce a2)
  | PAsn (Pred(e, name)) -> 
	    seqf(seval_mut0 e)
		(fun v -> sproduce_chunks (Chunks (v,name)))
  | IfAsn (b, a1, a2) -> fork (sassume0 b @> sproduce a1) (sassume0 (B_not b) @> sproduce a2)

let sheap_sub sheap chunk trm =
  (fun chnk ->
     if chnk=chunk then T_sub(sheap chnk, trm)
	 else sheap chnk
  )

let sconsume_chunks(c: chunks)=
  (fun (SState sstate) ->
    let (Pcond pcond,sstore,sheap)=sstate in
    let Chunks(count, name)=c in
    let f=F_and (F_neg(F_lt(count,T_lit 0)),F_neg(F_lt(sheap name,count))) in
    let formulae=(F_neg f)::pcond in
    if satisfiable formulae=true then (
 	printFormulae formulae;
	Angelic([])
)
    else
	Single(SState (Pcond pcond,sstore,sheap_sub sheap name count),Unit)
  )

let rec sconsume a=
  match a with
    BAsn b -> sassert b
  | AndAsn(a1, a2) -> (sconsume a1) @> (sconsume a2)
  | PAsn (Pred(e, pred)) -> 
	    seqf(seval_mut0 e)
		(fun v -> sconsume_chunks (Chunks (v,pred)))
  | IfAsn (b, a1, a2) ->  fork (sassume0 b @> sconsume a1) (sassume0 (B_not b) @> sconsume a2)

let empty_heap=
  (fun chnk -> T_lit 0)

let clear_heap=
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
    Single(SState (pcond,sstore,empty_heap),Unit)
  )

(*
==============================
TIME BUDGET
==============================
*)


let jump = 
  sconsume (PAsn(Pred(E_lit 2, "tb")))

let calfun =
  sconsume (PAsn(Pred(E_lit 8, "tb")))

let enter =
  sconsume (PAsn(Pred(E_lit 5, "tb")))

let leave =
  sconsume (PAsn(Pred(E_lit 7, "tb")))

exception Not_Supported of string;;

let rec cycle e=
  match e with
  | E_lit z -> 2
  | E_var v -> 3
  | E_add (e1, e2) -> cycle e1 + cycle e2
  | E_sub (e1, e2) -> cycle e1 + cycle e2
  | E_mul (e1, e2) -> raise (Not_Supported "mul is not supported") 

let rec cyclb b=
  match b with
  | B_eq (e1, e2) -> 1 + cycle e1 + cycle e2
  | B_lt (e1, e2) -> 1 + cycle e1 + cycle e2
  | B_not b -> cyclb b
  | B_and (b1, b2) -> raise (Not_Supported "and is not supported") 

let rec cycles es=
  match es with
    [] -> 0
  | h::t -> cycle h + cycles t

(*
==============================
STORE
==============================
*)

exception Different_Lengths of string;;

let rec do4list todo resource list1 list2=
  match list1 with
    [] -> resource
  | l1::l1rest ->
	match list2 with
	  [] -> raise (Different_Lengths "Lists With Different Lengths") 
	| l2::l2rest -> do4list todo (todo resource l1 l2) l1rest l2rest

let sstore_update sstore var trm =
  (fun v ->
     if v=var then trm
	 else sstore v
  )

let rec sstore_updates sstore vars trms =
  do4list sstore_update sstore vars trms

let seval_mut e=
  let cycl=cycle e in
  (sconsume (PAsn(Pred(E_lit cycl, "tb")))) @>
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
	let a=seval sstore e in
	Single(SState (pcond,sstore,h),a)
  )

let sevals_mut es=
  let cycls=cycles es in
  (sconsume (PAsn(Pred(E_lit cycls, "tb")))) @>
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
	let a=sevals sstore es in
	Single(SState (pcond,sstore,h),a)
  )

let sstore_update_mut var trm=
  (sconsume (PAsn(Pred(E_lit 3, "tb")))) @>
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
    let sstore2=sstore_update sstore var trm in
	Single(SState (pcond,sstore2,h),Unit)
  )

let sstore_update_mut0 var trm=
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
    let sstore2=sstore_update sstore var trm in
	Single(SState (pcond,sstore2,h),Unit)
  )

let get_store=
  (fun (SState sstate) ->
    let (_,sstore,_)=sstate in
	Single(SState sstate,sstore)
  )

let set_store s=
  (fun (SState sstate) ->
    let (pcond,sstore,h)=sstate in
	Single(SState (pcond,s,h),Unit)
  )

let with_store' s c=
  seqf (get_store) 
       (fun store1 -> 
		seq(set_store s)
		   ((c) @>
			(seqcomma(get_store)
			         (set_store store1)
			) 
		   )	
       )

let with_store s c=
  seqf (get_store) 
       (fun store1 -> 
		seq(set_store s)
		   ((c) @>
		    (set_store store1) 
		   )	
       )

let rec make_equality_fromulas terms=
  match terms with
    [] -> []
  | h::t -> ((F_eq(h,h))::(make_equality_fromulas t))

let make_equality_fromulas_mut terms=
  (fun (SState sstate) ->
    let (Pcond pcond1,sstore,h)=sstate in
    Single(SState (Pcond (List.append pcond1 (make_equality_fromulas terms)),sstore,h),Unit)
  )

let shavoc1 var=
  seqf (fresh_mut) 
       (fun fv -> 
          sstore_update_mut0 var fv @>
          make_equality_fromulas_mut [fv]
       )  

let store0 = fun _ -> T_lit 0

let noop=
  (fun (SState sstate) ->
      Single(SState sstate,Unit)
  )

let rec shavoc vars=
  match vars with
  | [] -> noop
  | t::h -> (shavoc1 t) @> (shavoc h)

(*
==============================
AUXILIARY DEFINITIONS
==============================
*)

let sassume b=
  (sconsume (PAsn(Pred(E_lit (cyclb(b)), "tb")))) @>
  (fun (SState sstate) ->
    let (Pcond pcond,sstore,h)=sstate in
    let bformula=sbeval sstore b in
    let formulas=bformula::pcond in
    if satisfiable formulas=true then 
      Single(SState (Pcond (bformula::pcond),sstore,h),Unit)
    else
        oblock
  )

let rec targets c=
  match c with
  | Assign (x, e) -> [x]
  | Call (x, r, es) -> [x]
  | IfCmd (b, c1, c2) -> union (targets c1)(targets c2)
  | While (b, inv, c) -> targets c
  | Seq (c1, c2) -> let u=union (targets c1)(targets c2) in u
  | Return (e) -> []
 
let get_routine_specification rtn=
  let routines_specifications = routines in
  let rec search rtn routines_specifications=(
    match routines_specifications with
      [] -> None
    | Rtn_def(routine_name, parameters, precondition, postcondition, commands)::t -> 
	if rtn=routine_name 
	then Some(Rtn_def(routine_name, parameters, precondition, postcondition, commands))
	else search rtn t
  ) in 
  search rtn routines_specifications

let result="result"
(*
==============================
SYMBOLIC EXECUTION
==============================
*)

let rec symexec c=
  match c with 
      Assign (v, e) ->
            (seqf (seval_mut e) (fun x -> sstore_update_mut v x))

    | Seq (c1, c2) ->
         (symexec c1) @> (symexec c2)

    | While (b,inv,c) ->
	(seqf(get_store)
	     (fun s ->
		with_store s (sconsume inv)
	     )
	) @>
	(shavoc (targets c)) @>
	fork ( 
		(clear_heap) @>
		(seqf(get_store)
		     (fun s ->
			with_store s (sproduce inv)
		     )
		) @>
		jump  @>		
		sassume b @>
		symexec c @>
		jump @>
		(seqf(get_store)
		     (fun s ->
			with_store s (sconsume inv)
		     )
		) @>
		block_mut
	     )
	     (
		jump @>
		(seqf(get_store)
		     (fun s ->
			with_store s (sproduce inv)
		     )
		) @>
		(sassume (B_not b)) 
	     )

    | IfCmd (b, c1, c2) ->
        fork 
	(
		sassume b @>
		jump @>
		symexec c1 @>
		jump
	)
	(
		sassume (B_not b) @>
		jump @>
		symexec c2 @>
		jump
	)

    | Return (e) ->
            (seqf(seval_mut e) 
		 (fun x -> 
			sstore_update_mut0 result x 
		 )
	    ) 

    | Call (var, rtn_name, args) ->
	match args with
          [] -> raise (Not_Supported "two parameters")
	| args -> 
	match get_routine_specification rtn_name with
	  None -> fail_mut
	| Some (Rtn_def(routine_name, params, precondition, postcondition, commands)) -> 
		(seqf(sevals_mut args)
		     (fun args_term ->
				calfun @>
				seqf(with_store' (sstore_updates store0 params args_term)
						 (sconsume precondition)
				    )
				    (fun store1 ->
					seqf(fresh_mut)
					    (fun t ->
						   (with_store (sstore_update store1 result t)
							       (sproduce (postcondition))
						   ) @>
						   (sstore_update_mut0 var t) @>
						   (make_equality_fromulas_mut [t])
					    )
				    ) 
		    ) 
		)

(*
==============================
VALID ROUTINE
==============================
*)

let rec numberOfBranches outcome =
  match outcome with
    Single(SState(pcond,sstore,h),out) -> 1
  | Angelic os -> 
	let rec os_branches os=
	  match os with 
	    [] -> 1
	  | h::t -> let n1 = numberOfBranches h in
		let n2 = os_branches t in
		n1+n2
          in
	os_branches os 
  | Demonic os -> 
	let rec os_branches os=
	  match os with 
	    [] -> 1
	  | h::t -> let n1 = numberOfBranches h in
		let n2 = os_branches t in
		n1+n2
          in
	os_branches os 


let rec correctness_check outcome =
  match outcome with
    Single(SState(pcond,sstore,h),out) -> true
  | Angelic os -> 
	let rec os_check os=
	  match os with 
	    [] -> false
	  | h::t -> correctness_check h || os_check t
          in
	os_check os 
  | Demonic os -> 
	let rec os_check os=
	  match os with 
	    [] -> true
	  | h::t -> correctness_check h && os_check t
          in
	os_check os 

let sstate0 = SState (Pcond [],store0,empty_heap)

let routine_valid rtn=
  let Rtn_def (name,paramvars,precondition,postcondition,cmd)=rtn in
  let m1=(
	      (seqf (fresh_muts paramvars) 
   	            (fun paramterms -> 
                      with_store (sstore_updates store0 paramvars paramterms)
		       (
			(make_equality_fromulas_mut paramterms) @>
			seqf(with_store' (sstore_updates store0 paramvars paramterms)
					 (sproduce precondition)
			    )
			    (fun s' ->
				  (enter) @>
				  (symexec cmd) @>
				  (seqf (seval_mut0 (E_var result))
					(fun t ->
					  with_store (sstore_update s' result t)
					  	     (sconsume postcondition) 
					)
				  ) @>
				  leave  
			    )
		       )
		    )
		) @>
		block_mut

	 ) in
  let outcome = m1 sstate0 in
  correctness_check outcome

let routine_valid2 rtn=
  let Rtn_def (name,paramvars,precondition,postcondition,cmd)=rtn in
  let m1=(
	      (seqf (fresh_muts paramvars) 
   	            (fun paramterms -> 
                      with_store (sstore_updates store0 paramvars paramterms)
		       (
			(make_equality_fromulas_mut paramterms) @>
			seqf(with_store' (sstore_updates store0 paramvars paramterms)
					 (sproduce precondition)
			    )
			    (fun s' ->
				  (enter) @>

				  (symexec cmd) @>

				  (seqf (seval_mut0 (E_var result))

					(fun t ->

					  with_store (sstore_update s' result t)

					  	     (sconsume postcondition) 

					)

				  ) @>

				  leave  
			    )
		       )
		    )
		) @>
		block_mut

	 ) in
  let outcome = m1 sstate0 in
  numberOfBranches outcome

let rec verify_program routines_specifications =
  match routines_specifications with
    [] -> Printf.printf "END\n\n"
  | routine::rest -> let Rtn_def (name,_,_,_,_)=routine in
		     let t1=Sys.time() in
		     let branches = routine_valid2 routine in
                     (if (routine_valid routine)=true 
			then (let t2=(Sys.time() -. t1) in Printf.printf "\n  %s IS SUCCESSFULLY VERIFIED :) in %f\n========================================================\n" name t2)
		      	else (let t2=(Sys.time() -. t1) in Printf.printf "\n  %s FAILED TO VERIFY :( in %f\n========================================================\n" name t2)
		     ); verify_program rest
;;

verify_program routines
;;


