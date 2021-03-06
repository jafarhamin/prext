 ____                _   
|  _ \ _ __ _____  _| |_ 
| |_) | '__/ _ \ \/ / __|
|  __/| | |  __/>  <| |_ 
|_|   |_|  \___/_/\_\\__|
                         
========================================== 

Prext-c is a non-optimizing compiler and assembler for the MSP430f5510 microcontroller written in OCaml that produces machine code with a predictable execution time where the number of cycles to execute the target code can be specified from the high-level source code. In addition to compiling the source code it puts some extra code to employ the timer register in order to store and display the number of cycles taken by the target code when using the MSP430-5510STK board. 

========================================== 
Syntax of the source code:
========================================== 

The syntax of the source code should be as follows where t* means an arbitrary number of repetitions of t, r is a routine name and x is a program variable.
s  ::=  t* m
where
t  ::=  routine r(x) req a ens a do c
m  ::=  routine main(x) req a ens a do c
and
c  ::=  x := e  |  if b then c else c  |  while b inv a do c |  x := r(e)  |  c; c  |  return e  |  ( c )
e  ::=  d  |  d + d |  d - d 
d  ::=  z  |  x
b  ::=  e = e  |  e < e
ex ::=  z  |  x  | ex + ex | ex - ex | ex * ex | ( ex )
bx ::=  ex = ex  |  ex < ex |  bx & bx  |  ! bx
a  ::=  bx  |  [ex]tb  |  a * a

You can find some simple examples in the file 'source.txt'

========================================== 
Execution time of the program:
========================================== 

The execution time of the program can be specified by the following formula:
cycle(s) = cycle(m)
where
cycle(m) = cycle(enter) + cycle(c) + cycle(leave)
cycle(if b then c1 else c2) = cycle(b) + 5 + cycle(c1) , if b evaluates to true
cycle(if b then c1 else c2) = cycle(b) + 5 + cycle(c2) , if b evaluates to false
cycle(while b inv a do c) = i * (5 + cycle(b) + cycle(c)) + 3 + cycle(b) , where i is the number of iterations of the loop
cycle(x := r(e)) = cycle(e) + cycle(call) + cycle(enter) + cycle(c) + cycle(leave) + cycle(x) , where c is the body of the r
cycle(c1; c2) = cycle(c1) + cycle(c2)
cycle(return e) = cycle(e) 
cycle(x := e) = 3 + cycle(e)
cycle(d1 + d2) = cycle(d1) + cycle (d2)
cycle(d1 - d2) = cycle(d1) + cycle (d2)
cycle(e1 < e2) = cycle(e1) + cycle (e2)
cycle(e1 = e2) = cycle(e1) + cycle (e2)
cycle(z) = 2
cycle(x) = 3
cycle(enter) = 5
cycle(leave) = 7
cycle(call) = 5

========================================== 
How to build:
========================================== 

The prerequisite: 
OCaml: Can be obtained by typing 'apt-get install ocaml-nox' on Ubuntu

To build the compiler:
1) Type 'make' on the terminal to make the executable file 'prextc'
2) Type 'make test' on the terminal to compile an example source code available in the file 'example_source_code.txt' in the folder 'example'. At this step the compiler produces two files, namely 'asmcode.asm'; the corresponding assembly file, and 'msp430code.txt'; the machine code file readable by msp430f5510. These files should be similar to their corresponding files in the folder 'example'.

========================================== 
How to use:
========================================== 

1) To compile your source code just copy it in the file 'source.txt'
2) Run the file 'prextc' to make the target file 'msp430code.txt' and the assembly file 'asmcode.asm'
3) Load the file 'msp430code.txt' onto the board 'MSP430-5510STK'. It can be accomplished by its appropriate software available on 'https://www.olimex.com/Products/MSP430/Starter/MSP430-5510STK/' 
4) The program is now executed on the board and then the LCD displays the number (c+10) where c is the number of cycles that takes the machine to execute the main routine of the program and 10 is for some initializations

Note that if you program the microcontroller by the file 'example_msp430_code.txt', the LCD displays '173' indicating it takes the machine 163 cycles to execute the main routine of the program in the file 'example_source_code.txt'.

========================================== 
Contact information:
========================================== 
You can find contact information on https://distrinet.cs.kuleuven.be/people/jafar

