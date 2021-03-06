 ____                _   
|  _ \ _ __ _____  _| |_ 
| |_) | '__/ _ \ \/ / __|
|  __/| | |  __/>  <| |_ 
|_|   |_|  \___/_/\_\\__| 
                         
========================================== 
Prext-v is a verification tool written in OCaml to verify execution time bounds of programs when compiling with prext-c compiler and executing on the MSP430f5510 microcontroller. This tool uses the Z3 theorem prover (and an overlay for the OCaml) to check the satisfiability of logical formulas produced by the symbolic execution of the input program. Each routine and loop in the source program should include a contract specifying execution time bound of the body of that routine and loop. Prext-v symbolically executes the program to verify these specifications and if all routines and loops satisfy their contracts it reports success. Otherwise it reports the routines that violate their contracts. The execution time bound is specified by [ex]tb where expression ex indicates the amount of time budget (or the number of cycles, from the machine point of view) devoted to that routine or loop.

========================================== 
Syntax of the source code:
========================================== 

The syntax of the source code should be as follows where t* means an arbitrary number of repetitions of t, r is a routine name and x is a program variable.
s  ::=  t* m
where
t  ::=  routine r(x) req a ens a do c
m  ::=  routine main(x) req a ens a do c
and
c  ::=  x := e  |  if b then c else c  |  while b inv a do c |  x := r(e)  |  c; c  |  return e
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

The execution time of a routine r with body c can be obtained by the following formula:
cycle(r) = cycle(enter) + cycle(c) + cycle(leave)
cycle(if b then c1 else c2) = cycle(b) + 5 + cycle(c1) , if b evaluates to true
cycle(if b then c1 else c2) = cycle(b) + 5 + cycle(c2) , if b evaluates to false
cycle(while b inv a do c) = i * (5 + cycle(b) + cycle(c)) + 3 + cycle(b) , where i is the number of iterations of the loop
cycle(x := r(e)) = cycle(e) + cycle(call) + cycle(enter) + cycle(c) + cycle(leave) + cycle(x) , where c is the body of the r
cycle(c1; c2) = cycle(c1) + cycle(c2)
cycle(return e) = cycle(e) 
cycle(x := e) = 3 + cycle(e)
cycle(d1 + d2) = cycle(d1) + cycle(d2)
cycle(d1 - d2) = cycle(d1) + cycle(d2)
cycle(e1 < e2) = cycle(e1) + cycle(e2)
cycle(e1 = e2) = cycle(e1) + cycle(e2)
cycle(z) = 2
cycle(x) = 3
cycle(enter) = 5
cycle(leave) = 7
cycle(call) = 5

========================================== 
How to build:
========================================== 
On Ubuntu 15.10
Run the following commands:
1) sudo apt-get install m4 opam
2) opam init
3) opam install Z3
4) make u1510
5) make test

On the earlier versions
1) Install Z3 theorem prover available on 'https://github.com/Z3Prover/z3'
2) Install z3overlay for the OCaml Z3 binding available on 'https://github.com/termite-analyser/z3overlay/tree/opt'
3) Replace 'z3-master' in the file 'make' with the path where the folder Z3 theorem is located
4) Type 'make' on the terminal to make the executable file 'prextv'
5) Type 'make test' on the terminal to see the result that should be similar to what is in the file 'report.txt'

========================================== 
How to use:
========================================== 

1) Copy your source code in the file 'source.txt'
2) Load the current folder to the library path by typing 'export LD_LIBRARY_PATH=$currentDir'
3) Run the executable file 'prextv'

Note that there is a source code example in the folder 'example'. Running the verification algorithm on this example results in something similar to the file 'report.txt' including a list of routines' names and the result of the verification algorithm on each routine.

========================================== 
Contact information:
========================================== 
You can find contact information on https://distrinet.cs.kuleuven.be/people/jafar

