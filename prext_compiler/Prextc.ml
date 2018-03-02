open Parser4prext;;

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
COMMANDS
==============================
*)

type label=string

type reg= string

type opr=
  Cnst of int
| Vari of string
| Regs of int
| Indx of (int * int)
| Inrg of int

type stm=
  Mov of (opr * opr)
| Add of (opr * opr)
| Sub of (opr * opr)
| Cmp of (opr * opr)
| Seq of (stm * stm)
| Jge of int
| Jne of int
| Jmp of int
| Lbl of int
| Rtn of int
| Cal of int
| Ret 

exception Not_Supported of string;;

let rec evalexpr e reg=
  match e with
      E_lit i -> Mov (Cnst i, reg)
    | E_var v -> Mov (Vari v, reg)
	| E_add (E_lit i, E_lit j) -> Seq (Mov (Cnst i, reg), Add (Cnst j, reg))
    | E_add (E_lit i, E_var v) -> Seq (Mov (Cnst i, reg), Add (Vari v, reg))
    | E_add (E_var v, E_lit i) -> Seq (Mov (Vari v, reg), Add (Cnst i, reg))
    | E_add (E_var v, E_var w) -> Seq (Mov (Vari v, reg), Add (Vari w, reg))
	| E_sub (E_lit i, E_lit j) -> Seq (Mov (Cnst i, reg), Sub (Cnst j, reg))
    | E_sub (E_lit i, E_var v) -> Seq (Mov (Cnst i, reg), Sub (Vari v, reg))
    | E_sub (E_var v, E_lit i) -> Seq (Mov (Vari v, reg), Sub (Cnst i, reg))
    | E_sub (E_var v, E_var w) -> Seq (Mov (Vari v, reg), Sub (Vari w, reg))
    | _ -> raise (Not_Supported "Not_Supported") 
	
let rec code_of_routine rtn rtninfo = 
    match rtninfo with
	    [] -> raise (Not_Supported "Not_Supported")
	  | h::t -> let (rtnname, code) = h in
			if rtn = rtnname then
				code
			else code_of_routine rtn t 
	
let rec compile c reg reg2 n rtninfo=
  match c with 
       Assign (v, e) ->
		(Seq (evalexpr e reg, Mov (reg, Vari v)),n)
	| IfCmd (b, c1, c2) ->
		(match b with 
		    B_lt (e1, e2) -> 
				let (cp1, n1)=compile c1 reg reg2 (n+1) rtninfo in
				let (cp2, n2)=compile c2 reg reg2 (n1+1) rtninfo in
				(Seq (evalexpr e1 reg, Seq (evalexpr e2 reg2, Seq (Cmp (reg2, reg),Seq(Jge n,Seq (cp1,Seq (Jmp (n1), Seq (Lbl n, Seq (cp2, Seq(Jmp (n1), Lbl n1))))))))),n2)
		  | B_eq (e1, e2) -> 
				let (cp1, n1)=compile c1 reg reg2 (n+1) rtninfo in
				let (cp2, n2)=compile c2 reg reg2 (n1+1) rtninfo in
				(Seq (evalexpr e1 reg, Seq (evalexpr e2 reg2, Seq (Cmp (reg2, reg),Seq(Jne n,Seq (cp1,Seq (Jmp (n1), Seq (Lbl n, Seq (cp2, Seq(Jmp (n1), Lbl n1))))))))),n2)
		  | _ -> raise (Not_Supported "Not_Supported")
		)
	| While (b, asn, c) ->
		(match b with 
		    B_lt (e1, e2) -> 
				let (cp1, n1)=compile c reg reg2 (n+2) rtninfo in
				(Seq (Lbl n, Seq (evalexpr e1 reg, Seq (evalexpr e2 reg2, Seq (Cmp (reg2, reg),Seq(Jge (n+1),Seq (cp1,Seq (Jmp n, Lbl (n+1)))))))),n1)
		  | B_eq (e1, e2) -> 
				let (cp1, n1)=compile c reg reg2 (n+2) rtninfo in
				(Seq (Lbl n, Seq (evalexpr e1 reg, Seq (evalexpr e2 reg2, Seq (Cmp (reg2, reg),Seq(Jne (n+1),Seq (cp1,Seq (Jmp n, Lbl (n+1)))))))),n1)
		  | _ -> raise (Not_Supported "Not_Supported")
		)
    | Seq (c1, c2) ->
		let (cp1, n1)=compile c1 reg reg2 n rtninfo in
		let (cp2, n2)=compile c2 reg reg2 n1 rtninfo in
        (Seq (cp1, cp2), n2)
	| Call (v,name,arg) -> 
		let rtncode = code_of_routine name rtninfo in
		(match arg with
		    [] -> (Seq (Cal rtncode, Mov (reg, Vari v)), n)
		  | h::t -> (Seq (evalexpr h reg, Seq (Cal rtncode, Mov (reg, Vari v))), n)
		)
	| Return e -> (Seq (evalexpr e reg, Seq (Add (Cnst 10, Regs 1), Ret)), n)
    | _ -> raise (Not_Supported "Not_Supported")

let compileroutine routine reg reg2 n rtninfo=
  let Rtn_def(routine_name, parameters, precondition, postcondition, commands)= routine in
  let newrtninfo=(routine_name, n)::rtninfo in
  match parameters with
      [] -> 
		let (cp, n2)= compile commands reg reg2 (n+1) newrtninfo in
		(Seq (Rtn n, Seq (Sub (Cnst 10, Regs 1), Seq(cp, Seq (Add (Cnst 10, Regs 1), Ret)))), n2, newrtninfo)
	| h::t -> 
		let (cp, n2)= compile commands reg reg2 (n+1) newrtninfo in
		(Seq (Rtn n, Seq (Sub (Cnst 10, Regs 1), Seq (Mov (reg, Vari h), Seq (cp, Seq (Add (Cnst 10, Regs 1), Ret))))), n2, newrtninfo)
		
let rec	compileroutines routines reg reg2 n rtninfo=
  match routines with
      [] -> ((Lbl n),n,rtninfo)
    | h::t -> 
		let (cr, n1, rtinf) = compileroutine h reg reg2 n rtninfo in
		let (crs, n2, rtinf2) = compileroutines t reg reg2 n1 rtinf in
		(Seq (cr, crs), n2, rtinf2)

let compile_program program =
	let (programcode, n, rtinfo) = compileroutines program (Regs 15) (Regs 14) 1 [] in
	let mainrtncode = code_of_routine "main" rtinfo in
	(Seq (Cal mainrtncode, Seq (Jmp n, programcode)), rtinfo)
	
let rec get_free_loc memory max=
  match memory with 
      [] -> max+2 
    | h::t -> let (var, memloc) = h in
		if memloc>max then get_free_loc t memloc
		else get_free_loc t max

let rec search_location varname memory=
  match memory with 
      [] -> None
    | h::t -> let (var, memloc) = h in
		if var=varname then Some memloc
		else search_location varname t

let locationof varname memory=
  match search_location varname memory with 
      None -> let freeloc = get_free_loc memory (-1) in
		(freeloc, (varname,freeloc)::memory)
	| Some loc -> (loc,memory)
		
let rec link asm memory sp=
  match asm with
      Mov (op1, op2) -> 
	    (
		match op1, op2 with
		    Vari (v1), Vari (v2) -> let (l1,m1)=locationof v1 memory in	
									let (l2,m2)=locationof v2 m1 in	
									(Mov (Indx (l1, sp), Indx (l2, sp)), m2)
		  | Vari (v1), _ -> let (l1,m1)=locationof v1 memory in	
									(Mov (Indx (l1, sp), op2), m1)
		  | _, Vari (v2) -> let (l2,m2)=locationof v2 memory in	
									(Mov (op1, Indx (l2, sp)), m2)
		  | _, _ -> (Mov (op1, op2), memory)
	    )
    | Add (op1, op2) -> 
	    (
		match op1, op2 with
		    Vari (v1), Vari (v2) -> let (l1,m1)=locationof v1 memory in	
									let (l2,m2)=locationof v2 m1 in	
									(Add (Indx (l1, sp), Indx (l2, sp)), m2)
		  | Vari (v1), _ -> let (l1,m1)=locationof v1 memory in	
									(Add (Indx (l1, sp), op2), m1)
		  | _, Vari (v2) -> let (l2,m2)=locationof v2 memory in	
									(Add (op1, Indx (l2, sp)), m2)
		  | _, _ -> (Add (op1, op2), memory)
	    )
    | Sub (op1, op2) -> 
	    (
		match op1, op2 with
		    Vari (v1), Vari (v2) -> let (l1,m1)=locationof v1 memory in	
									let (l2,m2)=locationof v2 m1 in	
									(Sub (Indx (l1, sp), Indx (l2, sp)), m2)
		  | Vari (v1), _ -> let (l1,m1)=locationof v1 memory in	
									(Sub (Indx (l1, sp), op2), m1)
		  | _, Vari (v2) -> let (l2,m2)=locationof v2 memory in	
									(Sub (op1, Indx (l2, sp)), m2)
		  | _, _ -> (Sub (op1, op2), memory)
	    )
	| Seq (c1, c2) -> let (cl1, m1) = link c1 memory sp in
						let (cl2, m2)=link c2 m1 sp in
						(Seq (cl1,cl2),m2)
	| Cmp (r1, r2) -> (Cmp (r1, r2), memory)
	| Jge lab -> (Jge lab, memory)
	| Jne lab -> (Jne lab, memory)
	| Jmp lab -> (Jmp lab, memory) 
	| Lbl lab -> (Lbl lab, memory)
	| Rtn lab -> (Rtn lab, [])
	| Cal lab -> (Cal lab, memory)
	| Ret -> (Ret, memory)
	| _ -> raise (Not_Supported "Not_Supported")
	  
let rcommands =
  let Rtn_def(routine_name, parameters, precondition, postcondition, commands)::t = routines in
  commands
;;

let asm_code = let (asmc,rtninf)=compile_program routines in asmc
let rtn_info = let (asmc,rtninf)=compile_program routines in rtninf

let asm_linked_code_memory = link asm_code [] 1
;;

let asm_linked_code=
	let (a,b)=asm_linked_code_memory in
	a
;;

let rec name_of_routine rtn rtninfo = 
    match rtninfo with
	    [] -> raise (Not_Supported "Not_Supported")
	  | h::t -> let (rtnname, code) = h in
			if rtn = code then
				rtnname
			else name_of_routine rtn t 

let print_opr opr=
  match opr with
      Regs r -> "R" ^ string_of_int r
    | Cnst i -> string_of_int i
    | Vari v -> v
    | Indx (i, r) -> (string_of_int i) ^ "(" ^ string_of_int r ^ ")"
    | Inrg i -> (string_of_int i) 

let rec print_asm_code code=
  match code with
    Mov (opr1, opr2) -> "MOV " ^ print_opr opr1 ^ ", " ^ print_opr opr2 ^ "\n"
  | Add (opr1, opr2) -> "ADD " ^ print_opr opr1 ^ ", " ^ print_opr opr2 ^ "\n"
  | Sub (opr1, opr2) -> "SUB " ^ print_opr opr1 ^ ", " ^ print_opr opr2 ^ "\n"
  | Cmp (opr1, opr2) -> "CMP " ^ print_opr opr1 ^ ", " ^ print_opr opr2 ^ "\n"
  | Seq (stm1, stm2) -> print_asm_code stm1 ^ print_asm_code stm2
  | Jge i -> "JGE L" ^ string_of_int i ^ "\n"
  | Jne i -> "JNE L" ^ string_of_int i ^ "\n"
  | Jmp i -> "JMP L" ^ string_of_int i ^ "\n"
  | Lbl i -> "L" ^ string_of_int i ^ " :\n"
  | Rtn i -> let rtn_name = name_of_routine i rtn_info in ";===========================\n; ROUTINE " ^ rtn_name ^ "\n;===========================\n" ^ "L" ^ string_of_int i ^ " :\n"
  | Cal i -> "CAL L" ^ string_of_int i ^ "\n"
  | Ret -> "RET" ^ "\n"


let asmcode= print_asm_code asm_linked_code

let op_code_of stm =
  match stm with 
      Mov (op1, op2) -> 4
    | Add (op1, op2) -> 5
    | Sub (op1, op2) -> 8
    | Cmp (op1, op2) -> 9
  	| _ -> raise (Not_Supported "Not_Supported") 	
	
let src_of_opr opr=
  match opr with
      Regs r -> r
    | Cnst i -> 0
	| Indx (i, r) -> 1
	| Inrg r -> r
 	| _ -> raise (Not_Supported "Not_Supported")

let operand_of_opr opr=
  match opr with
      Regs r -> None
    | Cnst i -> Some i
	| Indx (i, r) -> Some i
	| Inrg i -> None
 	| _ -> raise (Not_Supported "Not_Supported")

let dst_of_opr opr=
  match opr with
      Regs r -> r
	| Indx (i, r) -> 1
 	| _ -> raise (Not_Supported "Not_Supported")
	
let bits_of_src opr=
  match opr with
      Regs r -> 0
    | Cnst i -> 3
	| Indx (i, r) -> 1
	| Inrg i -> 2
 	| _ -> raise (Not_Supported "Not_Supported")

let bits_of_dst opr=
  match opr with
      Regs r -> 0
	| Indx (i, r) -> 1
 	| _ -> raise (Not_Supported "Not_Supported")

let bits_of_stm op1 op2=
  let srcb = bits_of_src op1 in
  let dstb = bits_of_dst op2 in
  dstb*8+srcb

let hex_of_dec_15 i=
  if (i<10) then (string_of_int i)
  else if (i=10) then "A"
  else if (i=11) then "B"
  else if (i=12) then "C"
  else if (i=13) then "D"
  else if (i=14) then "E"
  else if (i=15) then "F"
  else "*ERROR*"

let rec hex_of_dec i=
  if i<16 then (hex_of_dec_15 i)                     	
  else (
  let j = i/16 in
  let r = i mod 16 in
  (hex_of_dec j) ^ (hex_of_dec_15 r)
  )

let rec fill_to n str=
  let l=String.length str in
  if n=l then str
  else "0" ^ (fill_to (n-1) str)
;;
  
let rev str=
  if String.length str = 4 then
  (String.sub str 2 2) ^ " " ^ (String.sub str 0 2) ^ " "
  else str
  
let opreand_of_opr_str opr=
  match operand_of_opr opr with
	  None -> ""
    | Some i -> (fill_to 4 (hex_of_dec i)) 
	
let labeltostr l = 
  let str = string_of_int l in
  fill_to 4 str

let rec instruction_code_of stms =
  match stms with 
      Mov (op1, op2) ->
 	  rev((hex_of_dec_15 (op_code_of stms)) ^ (hex_of_dec_15 (src_of_opr op1)) ^ (hex_of_dec_15 (bits_of_stm op1 op2)) ^ (hex_of_dec_15 (dst_of_opr op2))) ^ (rev(opreand_of_opr_str op1)) ^ (rev(opreand_of_opr_str op2)) 
    | Add (op1, op2) -> 
 	  rev((hex_of_dec_15 (op_code_of stms)) ^ (hex_of_dec_15 (src_of_opr op1)) ^ (hex_of_dec_15 (bits_of_stm op1 op2)) ^ (hex_of_dec_15 (dst_of_opr op2))) ^ (rev(opreand_of_opr_str op1)) ^ (rev(opreand_of_opr_str op2))
    | Sub (op1, op2) -> 
 	  rev((hex_of_dec_15 (op_code_of stms)) ^ (hex_of_dec_15 (src_of_opr op1)) ^ (hex_of_dec_15 (bits_of_stm op1 op2)) ^ (hex_of_dec_15 (dst_of_opr op2))) ^ (rev(opreand_of_opr_str op1)) ^ (rev(opreand_of_opr_str op2))
    | Cmp (op1, op2) -> 
	  rev((hex_of_dec_15 (op_code_of stms)) ^ (hex_of_dec_15 (src_of_opr op1)) ^ (hex_of_dec_15 (bits_of_stm op1 op2)) ^ (hex_of_dec_15 (dst_of_opr op2))) 
    | Seq (c1, c2) -> (instruction_code_of c1) ^ (instruction_code_of c2)
	| Lbl l -> "#" ^ (string_of_int l) ^ "* "
	| Rtn l -> "#" ^ (string_of_int l) ^ "* "
    | Jge l -> "G" ^ (labeltostr l) ^ " "
    | Jne l -> "N" ^ (labeltostr l) ^ " "
    | Jmp l -> "P" ^ (labeltostr l) ^ " "
    | Cal l -> "I" ^ (labeltostr l) ^ " $$ $$ "
    | Ret -> "10 01 "

let mcode = instruction_code_of asm_linked_code;;

let rec labeladress mcode n=
  if String.contains mcode '#' then
    let l=String.length mcode in
    let index= String.index mcode '#' in 
    if String.contains (String.sub mcode index (l-index)) '*' then
      let endindex=String.index mcode '*' in
      if index mod 3 <> 0 then 
	    raise (Not_Supported "Not_Supported")
	  else 
	  let entry = (fill_to 4 (String.sub mcode (index+1)(endindex-index-1)),(n+index)/3) in
	  if endindex >= l-2 then 
		[entry]
	  else
		entry::(labeladress (String.sub mcode (endindex+2) (l-endindex-2)) (n+index))
	else raise (Not_Supported "Not_Supported")
  else []

let labelsaddress = labeladress mcode 0

let rec removelabels mcode=
  if String.contains mcode '#' then
    let l=String.length mcode in
    let index= String.index mcode '#' in
    if String.contains (String.sub mcode index (l-index)) '*' then
      let endindex=String.index mcode '*' in
	  if endindex>=l-2 then 
		(String.sub mcode 0 index)
	  else
	    (String.sub mcode 0 index) ^ (removelabels (String.sub mcode (endindex+2) (l-endindex-2)))
	else raise (Not_Supported "Not_Supported")
  else mcode
  
let rlmcode = removelabels mcode
  
let rec absolute_address_of lblstr labelsaddress = 
    match labelsaddress with
	    [] -> raise (Not_Supported "Not_Supported")
	  | h::t -> let (lbl, addr) = h in
			if lbl = lblstr then
				addr
			else absolute_address_of lblstr t 

let rec bin_of_dec i =
  if i<2 then string_of_int i                     	
  else (
  let j = i/2 in
  let r = i mod 2 in
  (bin_of_dec j) ^ (string_of_int r)
  )  

let bin_of_dec_10 i =
  let b = bin_of_dec i in
  fill_to 10 b

let chartoint ch=
  if ch='0' then 0
  else if ch='1' then 1
  else if ch='2' then 2
  else if ch='3' then 3
  else raise (Not_Supported "Not_Supported")

let compb b =
  if b='0' then "1"
  else if b='1' then "0"
  else raise (Not_Supported "Not_Supported")
  
  
let rec comp b=
  let l=String.length b in
  let fb=String.get b 0 in
  if l=1 then compb fb
  else (compb fb) ^ (comp (String.sub b 1 (l-1)))
  
let rec inc_one_bin b=
  let l=String.length b in
  if l=1 then "0"
  else if (String.get b (l-1)) = '0' then (String.sub b 0 (l-1)) ^ "1"
  else (inc_one_bin (String.sub b 0 (l-1))) ^ "0"


let rec dec_of_bin b = 
  let l=String.length b in
  let i=chartoint (String.get b (l-1)) in
  if l=1 then i
  else i + 2 * (dec_of_bin (String.sub b 0 (l-1)))
  
let hex_of_signed_dec_10_bit i = 
  if (i>=0) then (fill_to 3 (hex_of_dec i))
  else 
  let bn = bin_of_dec_10 (-1*i) in
  let bc = comp bn in
  let b1 = inc_one_bin bc in
  let dc = dec_of_bin b1 in
  hex_of_dec dc
;;
  
let mix hexofs opc bit2= 
  let ch=String.get hexofs 0 in
  let i=chartoint ch in
  (String.sub hexofs 1 2) ^ " " ^ opc ^ (hex_of_dec (bit2+i)) ^ " "
 
;;

let mixforcalls absaddr=
  let absaddrs = absaddr + 34022 in
  let absaddrshex = rev(fill_to 4 (hex_of_dec absaddrs)) in
  "B0 13 " ^ absaddrshex
			
let rec organizejmps ch mcode opc bit2 n=
  if String.contains mcode ch then
    let l=String.length mcode in
    let offsindex= String.index mcode ch in
	let index= offsindex+n in 
	if index mod 3 <> 0 then raise (Not_Supported "Not_Supported")
	else
	let lblstr=String.sub mcode (offsindex+1) 4 in
	let ft = fill_to 4 lblstr in 
	let absaddr= absolute_address_of ft labelsaddress in
	let offset1= absaddr-(index/3) in
	let offset2= (offset1-2)/2 in
	if ch='I' then 
		let code = mixforcalls absaddr in
		if offsindex + 8 >= l then (String.sub mcode 0 offsindex) ^ code 
		else
			(String.sub mcode 0 offsindex) ^ code ^ (organizejmps ch (String.sub mcode (offsindex+12) (l-offsindex-12)) opc bit2 (n+offsindex+12))
		
	else 
		let code= mix (hex_of_signed_dec_10_bit offset2) opc bit2 in
		if offsindex + 8 >= l then (String.sub mcode 0 offsindex) ^ code 
		else
			(String.sub mcode 0 offsindex) ^ code ^ (organizejmps ch (String.sub mcode (offsindex+6) (l-offsindex-6)) opc bit2 (n+offsindex+6))
		
  else mcode

let wjmcode = 
  let jmps = organizejmps 'P' rlmcode "3" 12 0 in
  let jlts = organizejmps 'G' jmps "3" 4 0 in
  let neqs = organizejmps 'N' jlts "2" 0 0 in
  organizejmps 'I' neqs "2" 0 0
;;

let organize str n= 
   let rec org str=
   (
   let l=String.length str in
   if l<=48 then str
   else
    (String.sub str 0 48)  ^ "\n" ^ (org (String.sub str 48 (l-48)))
   )in
   let l=String.length str in
   if l<=12 then str
   else
     let offs=3*n in
    (String.sub str 0 offs)  ^ "\n" ^ (org (String.sub str offs (l-offs))) 
;;

let rec iterstr str n=
  if n=0 then ""
  else str ^ (iterstr str (n-1))

let c i o = rev(fill_to 4 (hex_of_dec (i+o-12)))

let firstpart o code = 
"21 82 C1 43 00 00 E2 D3 42 02 3C 40 50 C3 0D 43 B0 13 " ^ (c 34592 o)^ "E2 C3 02 02 E2 C2 02 02 D1 42 00 02 02 00 3F 40 0F 00 5F F1 02 00 C1 4F 00 00 3F 40 30 00 6F D1 C1 4F 01 00 1F 43 5F D1 01 00 C2 4F 02 02 F2 D2 02 02 3C 40 05 00 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 B0 13 " ^ (c 34592 o)^ "3C 40 F4 01 B0 13 " ^ (c 34592 o)^ "D1 42 00 02 02 00 3F 40 0F 00 5F F1 02 00 C1 4F 00 00 3F 40 30 00 6F D1 C1 4F 01 00 1F 43 5F D1 01 00 C2 4F 02 02 F2 D2 02 02 3C 40 05 00 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 B0 13 " ^ (c 34592 o)^ "3C 40 F4 01 B0 13 " ^ (c 34592 o)^ "D1 42 00 02 02 00 3F 40 0F 00 5F F1 02 00 C1 4F 00 00 3F 40 30 00 6F D1 C1 4F 01 00 1F 43 5F D1 01 00 C2 4F 02 02 F2 D2 02 02 3C 40 05 00 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 B0 13 " ^ (c 34592 o)^ "3C 40 F4 01 B0 13 " ^ (c 34592 o)^ "D1 42 00 02 02 00 3F 40 0F 00 5F F1 02 00 C1 4F 00 00 3F 40 20 00 6F D1 C1 4F 01 00 1F 43 5F D1 01 00 C2 4F 02 02 F2 D2 02 02 3C 40 05 00 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 B0 13 " ^ (c 34592 o)^ "7C 40 28 00 B0 13 52 82 7C 42 B0 13 52 82 5C 43 B0 13 52 82 7C 40 06 00 B0 13 52 82 7C 40 0C 00 B0 13 52 82 21 52 10 01 4A 14 21 82 C7 0E C6 0D C8 0C 39 40 1F 00 09 58 81 49 00 00 81 43 02 00 3D 40 20 00 3E 40 20 00 B0 13 " ^ (c 34830 o)^ "2F 41 CF 43 00 00 3E 40 1E 00 0E 58 81 4E 00 00 0A 43 5F 46 06 00 3F 80 25 00 0C 24 3F 80 3E 00 19 24 1F 83 0F 24 3F 80 0B 00 0C 24 3F 80 09 00 09 24 1C 3C CC 08 3D 40 " ^ (c 34940 o)^ "2E 43 B0 13 " ^ (c 34868 o)^ "1C 43 50 3C CC 06 CD 01 2D 53 CE 01 CF 07 B0 13 " ^ (c 34396 o)^ "0C 3C A7 53 00 00 2F 47 5F 4F FE FF 4F 93 01 20 1A 43 CE 4F 00 00 91 83 00 00 81 93 02 00 06 24 2F 41 FF 40 2D 00 00 00 91 83 00 00 CF 09 2F 81 1F 93 04 34 C9 08 09 8F 19 53 01 3C C9 08 1D 43 2D 51 CC 09 0E 43 3F 40 20 00 B0 13 " ^ (c 34736 o)^ "81 4C 00 00 0A 93 06 24 CF 0C 1F 53 81 4F 00 00 CC 43 00 00 28 91 0B 28 2C 41 1C 83 CE 08 2E 81 1E 53 3D 40 20 00 B0 13 " ^ (c 34830 o)^ "C8 43 00 00 CE 09 0E 88 CC 08 3D 40 20 00 B0 13 " ^ (c 34830 o)^ "CC 08 B0 13 " ^ (c 34886 o)^ "0C 5A 21 52 46 16 10 01 31 80 06 00 C1 4C 00 00 C1 43 01 00 C1 43 02 00 3C 40 F4 01 0D 43 B0 13 " ^ (c 34592 o)^ "3F 40 F0 00 6F F1 C1 4F 01 00 D1 42 00 02 04 00 3F 40 0F 00 5F F1 04 00 C1 4F 02 00 5F 41 02 00 5F D1 01 00 C1 4F 03 00 1F 43 5F D1 03 00 C2 4F 02 02 E2 C2 02 02 E2 C3 02 02 F2 D2 02 02 3C 40 05 00 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 3F 40 0F 00 6F F1 C1 4F 01 00 5F 41 01 00 43 18 4F 5F C1 4F 01 00 F1 F0 F0 00 01 00 D1 42 00 02 04 00 3F 40 0F 00 5F F1 04 00 C1 4F 02 00 5F 41 02 00 5F D1 01 00 C1 4F 03 00 1F 43 5F D1 03 00 C2 4F 02 02 E2 C2 02 02 E2 C3 02 02 F2 D2 02 02 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 3C 40 64 00 B0 13 " ^ (c 34592 o)^ "31 50 06 00 10 01 31 80 06 00 C1 4C 00 00 C1 43 01 00 C1 43 02 00 3F 40 F0 00 6F F1 C1 4F 01 00 D1 42 00 02 04 00 3F 40 0F 00 5F F1 04 00 C1 4F 02 00 5F 41 02 00 5F D1 01 00 C1 4F 03 00 1F 43 5F D1 03 00 C2 4F 02 02 E2 C2 02 02 E2 D3 02 02 F2 D2 02 02 3C 40 05 00 0D 43 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 3F 40 0F 00 6F F1 C1 4F 01 00 5F 41 01 00 43 18 4F 5F C1 4F 01 00 F1 F0 F0 00 01 00 D1 42 00 02 04 00 3F 40 0F 00 5F F1 04 00 C1 4F 02 00 5F 41 02 00 5F D1 01 00 C1 4F 03 00 1F 43 5F D1 03 00 C2 4F 02 02 E2 C2 02 02 E2 D3 02 02 F2 D2 02 02 B0 13 " ^ (c 34592 o)^ "F2 C2 02 02 3C 40 F4 01 B0 13 " ^ (c 34592 o)^ "31 50 06 00 10 01 5A 14 31 80 30 00 C9 0F C6 0E 81 4D 06 00 CA 0C 37 01 4C 00 25 4A 2C 4A B0 13 " ^ (c 34886 o)^ "C8 0C 08 55 81 43 04 00 05 98 46 2C 81 43 08 00 C1 43 0E 00 0D 3C 2F 4A CF 93 00 00 3D 24 CE 0F 1E 53 8A 4E 00 00 6C 4F CD 06 49 13 91 53 04 00 3E 40 25 00 2F 4A 6E 9F EE 23 9A 53 00 00 2F 4A CE 0F 1E 53 8A 4E 00 00 6F 4F C1 4F 0E 00 3F 90 73 00 13 24 CC 01 3C 50 10 00 CD 01 3D 52 CE 01 3E 50 06 00 B0 13 44 81 CE 0C CC 01 3C 50 10 00 CD 06 47 13 81 5C 04 00 0C 3C 71 09 00 00 CC 01 3C 52 CD 06 CE 01 3E 50 06 00 CF 01 2F 52 B0 13 " ^ (c 34472 o)^ "8A 98 00 00 BA 2B 1C 41 04 00 31 50 30 00 55 16 10 01 31 80 1A 00 B2 40 80 5A 5C 01 D2 43 02 02 F2 40 FE 00 04 02 E2 43 48 02 E2 43 42 02 F2 40 03 00 44 02 03 43 32 D2 03 43 B0 13 00 80 3C 40 10 27 0D 43 B0 13 " ^ (c 34592 o)^ "B0 13 " ^ (c 34900 o)^ "B2 D0 14 02 80 03 B2 43 92 03 82 43 90 03 " ^ code ^ "91 42 90 03 04 00 B1 40 " ^ (c 34942 o)^ "00 00 91 41 04 00 02 00 CC 01 3C 50 0A 00 B0 13 " ^ (c 34536 o)^ "5C 43 CD 01 3D 50 0A 00 B0 13 " ^ (c 34208 o)^ "31 50 1A 00 10 01 3A 14 19 42 5C 01 B2 40 80 5A 5C 01 3F 40 00 00 3F 90 00 00 21 24 3F 40 00 00 3F 90 00 00 1C 24 3A 40 00 00 3A 80 00 00 5A 09 38 40 00 00 3C 48 3D 48 3E 48 3F 48 C7 0C CB 0D 1C 53 0D 63 0F 18 4B 5B 00 18 4B D7 6B 4B 4B 4B 5B 06 00 18 5B 4B 00 00 4B 13 1A 83 EB 23 79 C2 39 D0 08 5A 82 49 5C 01 3F 40 00 00 3F 90 00 00 08 24 3A 40 00 00 02 3C 6A 13 2A 52 3A 90 00 00 FB 23 37 16 10 01 31 80 06 00 81 4D 02 00 C1 4C 00 00 C1 43 04 00 F1 90 03 00 00 00 26 2C 5C 43 B0 13 52 82 6C 43 B0 13 52 82 7C 40 80 00 B0 13 52 82 D1 93 00 00 05 20 7C 40 80 00 B0 13 52 82 0F 3C 7C 40 C0 00 B0 13 52 82 0A 3C 6C 4F B0 13 1C 83 91 53 02 00 D1 53 04 00 F1 92 04 00 05 2C 1F 41 02 00 CF 93 00 00 F1 23 31 50 06 00 10 01 2A 14 CA 0F C9 0D CB 0C 0B 93 09 20 2E 4A CF 0E 1F 83 8A 4F 00 00 FE 40 30 00 00 00 15 3C CC 0B CD 09 B0 13 " ^ (c 34684 o)^ "C8 0C 2F 4A CE 0F 1E 83 8A 4E 00 00 CD 09 B0 13 " ^ (c 34808 o)^ "0B 8C 3B 50 " ^ (c 34922 o)^ "EF 4B 00 00 CB 08 0B 93 EB 23 2C 4A B0 13 " ^ (c 34886 o)^ "28 16 10 01 1A 14 CB 0D CD 0F CA 0C 5F 4A 06 00 3F 80 6F 00 09 24 3F 80 09 00 03 24 39 40 0A 00 04 3C 39 40 10 00 01 3C 39 42 B0 13 " ^ (c 34638 o)^ "5F 4A 06 00 3F 90 64 00 06 20 0C 93 04 34 9B 43 00 00 3C E3 1C 53 CD 09 CF 0E B0 13 " ^ (c 34314 o)^ "19 16 10 01 3A 14 C7 0F C8 0D 39 01 14 00 AE 53 00 00 2F 4E 1A 4F FE FF 0A 93 10 24 CC 0A B0 13 " ^ (c 34886 o)^ "87 5C 00 00 1C 93 0B 38 1A 83 C7 0C 1A 53 6C 4A CD 08 49 13 17 83 FA 23 02 3C 4C 43 49 13 37 16 10 01 31 82 91 41 0C 00 04 00 81 4C 06 00 00 18 F1 40 " ^ (c 34762 o)^ "00 00 CD 01 3D 50 0E 00 CC 01 2C 52 CE 01 3E 50 06 00 8F 00 " ^ (c 34850 o)^ "B0 13 DE 83 1F 41 06 00 CF 43 00 00 31 52 10 01 21 82 81 4C 00 00 81 4D 02 00 81 93 02 00 03 20 81 93 00 00 0A 24 91 83 00 00 81 73 02 00 81 93 02 00 F9 23 81 93 00 00 F6 23 21 52 10 01 5F 4C 06 00 7F 90 70 00 0C 24 4F 4F 3F 80 64 00 08 24 3F 80 0B 00 05 24 3F 80 09 00 02 24 0C 43 10 01 AD 53 00 00 2F 4D 1C 4F FE FF 10 01 CF 0D 3F 82 03 24 3F 82 03 24 04 3C 5C 0B 10 01 5C 0F 10 01 80 00 " ^ (c 34786 o)^ "10 01 31 40 00 34 B0 13 " ^ (c 34914 o)^ "0C 93 02 24 B0 13 " ^ (c 34080 o)^ "0C 43 B0 13 9E 84 B0 13 " ^ (c 34918 o)^ "1F 93 09 38 6B 4D 1C 53 CC 4B FF FF 0B 9E 04 24 1D 53 1F 83 F7 23 0C 43 10 01 1A 14 CA 0E C9 0D CD 0C 2C 49 B0 13 " ^ (c 34868 o)^ "89 5A 00 00 CC 0A 19 16 10 01 0E 43 0F 4C 1C 43 5F 02 0E 6E 0E 9D 01 28 0E 8D 0C 6C F9 2B 10 01 02 12 32 C2 03 43 82 4C C0 04 82 4D C8 04 1C 42 CA 04 32 41 10 01 CF 0C 0E 93 06 24 4D 4D 1F 53 CF 4D FF FF 1E 83 FB 23 10 01 2E 4D CF 0E 1F 53 8D 4F 00 00 CE 4C 00 00 4C 4C 10 01 CF 0C 0E 93 05 24 1F 53 FF 4D FF FF 1E 83 FB 23 10 01 3F 43 1F 53 7E 4C 0E 93 FC 23 CC 0F 10 01 5C 43 B0 13 52 82 10 01 32 D0 10 00 FD 3F 1C 43 10 01 03 43 FF 3F 30 31 32 33 34 35 36 37 38 39 61 62 63 64 65 66 00 00 25 00 25 64 00 00" 

let putalltogether code =
  let offset = (String.length code /3) in
  let fp = organize (firstpart offset code) 0 in
  let sp = organize ((iterstr (c 34908 offset) 22) ^ (c 34710 offset)) 0 in
  ("@8000" ^ fp ^ " \n@ffd2" ^ sp ^ "\nq")

let output = putalltogether wjmcode

open Printf
  
let write_to_file2 file strs =
  let oc = open_out file in    
  let rec rpt strs = (
    match strs with
	    [] -> fprintf oc ""
	  | h::t -> fprintf oc "%s\n" h; rpt t
  ) in
  rpt strs;
  close_out oc;                
;;

let write_to_file file str =
  let oc = open_out file in    
  fprintf oc "%s\n" str;
  close_out oc;                
;;

write_to_file "asmcode.asm" asmcode;;
write_to_file "msp430code.txt" output;;

