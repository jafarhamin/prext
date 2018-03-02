CAL L35
JMP L36
;===========================
; ROUTINE bar
;===========================
L1 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
ADD 10, R1
RET
;===========================
; ROUTINE foo
;===========================
L2 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
L3 :
MOV 3(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L4
MOV 3(1), R15
ADD 1, R15
MOV R15, 3(1)
JMP L3
L4 :
MOV 1, R15
CAL L1
MOV R15, 5(1)
ADD 10, R1
RET
;===========================
; ROUTINE square1
;===========================
L5 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
MOV 0, R15
MOV R15, 5(1)
L6 :
MOV 5(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L7
MOV 3(1), R15
ADD 1(1), R15
MOV R15, 3(1)
MOV 5(1), R15
ADD 1, R15
MOV R15, 5(1)
JMP L6
L7 :
MOV 3(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE square2
;===========================
L8 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
MOV 0, R15
MOV R15, 5(1)
L9 :
MOV 5(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L10
MOV 3(1), R15
ADD 1(1), R15
MOV R15, 3(1)
MOV 5(1), R15
ADD 1, R15
MOV R15, 5(1)
JMP L9
L10 :
MOV 3(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE square3
;===========================
L11 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
MOV 0, R15
MOV R15, 5(1)
L12 :
MOV 5(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L13
MOV 3(1), R15
ADD 1(1), R15
MOV R15, 3(1)
MOV 5(1), R15
ADD 1, R15
MOV R15, 5(1)
JMP L12
L13 :
MOV 3(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE square4
;===========================
L14 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
MOV 0, R15
MOV R15, 5(1)
L15 :
MOV 5(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L16
MOV 3(1), R15
ADD 1(1), R15
MOV R15, 3(1)
MOV 5(1), R15
ADD 1, R15
MOV R15, 5(1)
JMP L15
L16 :
MOV 3(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE loopSum
;===========================
L17 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
MOV 0, R15
MOV R15, 5(1)
L18 :
MOV 5(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L19
MOV 5(1), R15
ADD 1, R15
MOV R15, 5(1)
MOV 3(1), R15
ADD 5(1), R15
MOV R15, 3(1)
JMP L18
L19 :
MOV 3(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE loopOddSum
;===========================
L20 :
SUB 10, R1
MOV R15, 1(1)
MOV 1, R15
MOV R15, 3(1)
MOV 1, R15
MOV R15, 5(1)
L21 :
MOV 5(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L22
MOV 5(1), R15
ADD 2, R15
MOV R15, 5(1)
MOV 3(1), R15
ADD 5(1), R15
MOV R15, 3(1)
JMP L21
L22 :
MOV 3(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE recSum1
;===========================
L23 :
SUB 10, R1
MOV R15, 1(1)
MOV 1(1), R15
MOV 1, R14
CMP R14, R15
JNE L24
MOV 1, R15
ADD 10, R1
RET
JMP L25
L24 :
MOV 1(1), R15
SUB 1, R15
CAL L23
MOV R15, 3(1)
MOV 1(1), R15
ADD 3(1), R15
ADD 10, R1
RET
JMP L25
L25 :
ADD 10, R1
RET
;===========================
; ROUTINE recSum2
;===========================
L26 :
SUB 10, R1
MOV R15, 1(1)
MOV 1(1), R15
MOV 1, R14
CMP R14, R15
JNE L27
MOV 1, R15
ADD 10, R1
RET
JMP L28
L27 :
MOV 1(1), R15
SUB 1, R15
CAL L26
MOV R15, 3(1)
MOV 1(1), R15
ADD 3(1), R15
ADD 10, R1
RET
JMP L28
L28 :
ADD 10, R1
RET
;===========================
; ROUTINE recIsOdd
;===========================
L29 :
SUB 10, R1
MOV R15, 1(1)
MOV 1(1), R15
MOV 2, R14
CMP R14, R15
JGE L30
MOV 1(1), R15
ADD 10, R1
RET
JMP L31
L30 :
MOV 1(1), R15
SUB 2, R15
CAL L29
MOV R15, 3(1)
MOV 3(1), R15
ADD 10, R1
RET
JMP L31
L31 :
ADD 10, R1
RET
;===========================
; ROUTINE loopFib
;===========================
L32 :
SUB 10, R1
MOV R15, 1(1)
MOV 0, R15
MOV R15, 3(1)
MOV 1, R15
MOV R15, 5(1)
MOV 1, R15
MOV R15, 7(1)
MOV 2, R15
MOV R15, 9(1)
L33 :
MOV 9(1), R15
MOV 1(1), R14
CMP R14, R15
JGE L34
MOV 5(1), R15
MOV R15, 3(1)
MOV 7(1), R15
MOV R15, 5(1)
MOV 3(1), R15
ADD 5(1), R15
MOV R15, 7(1)
MOV 9(1), R15
ADD 1, R15
MOV R15, 9(1)
JMP L33
L34 :
MOV 7(1), R15
ADD 10, R1
RET
ADD 10, R1
RET
;===========================
; ROUTINE main
;===========================
L35 :
SUB 10, R1
MOV R15, 1(1)
MOV 5, R15
CAL L32
MOV R15, 1(1)
ADD 10, R1
RET
L36 :

