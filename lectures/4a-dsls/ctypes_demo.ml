(**
   The following code can be run using a recent version of ocaml (e.g. 4.07).
   First install OPAM, then run the following commands to install an OCaml
   compiler and the ctypes packages:

      opam switch 4.07.1
      eval $(opam config env)
      opam install ctypes ctypes-foreign
 *)

#use "topfind";;
#require "ctypes.stubs";;
#require "ctypes.foreign";;

open Ctypes;;

(** Ctypes treats C types as an embedded DSL.  There's a constructor
    for each C type and type family: int, float, pointer, array, etc. *)
int;;
float;;
complex64;;
ptr (array 3 (ptr int));;

(** It's also possible to build types representing structures.
    Here's a description of a struct 's' with two fields, 'x' and 'y'.
 *)
let s : [`s] structure typ = structure "foo";;
let x = field s "x" int;;
let y = field s "y" float;;
seal s;;
let v = make s;; (* Allocate a value of struct 's' *)
setf v y 4.5;;
setf v x 3;;

(** The 'Foreign' module supports binding C functions
    so that they can be called from OCaml programs *)
open Foreign;;

(** Each function is bound by passing its name as a string
    to 'foreign', along with a value representing its type.

    The two constructors '@->' and 'returning' make it possible
    to construct representations of function types *)
let strlen = foreign "strlen" (string @-> returning int);;
let puts = foreign "puts" (string @-> returning int);;
let sqrt = foreign "sqrt" (double @-> returning double);;
let pow = foreign "pow" (double @-> double @-> returning double);;

(** Once functions are bound they can be called immediately *)
puts "Hello, world";;
pow 3.0 4.0;;

(** It's also possible to give multiple interpretations to type
   representations.  We'll abstract over the language of type
   constructors in order to do so.  (In fact, we only need
   to abstract over '@->', 'returning', and 'foreign', and
   their types, not the constructors for basic types such as
   'int' and 'float'
*)
module type FOREIGN =
sig
  type 'a fn
  type 'a return
  val (@->) : 'a typ -> 'b fn -> ('a -> 'b) fn
  val returning : 'a typ -> 'a return fn

  type 'a result
  val foreign : string -> ('a -> 'b) fn -> ('a -> 'b) result
end

(** Now we can write foreign function bindings that
    are abstracted over the interpretation of 'foreign',
    '@->' and 'returning' *)
module My_functions(F: FOREIGN) =
struct
  open F
  let pow = foreign "pow" (double @-> double @-> returning double)
  let puts = foreign "puts" (string @-> returning int)
  let chdir = foreign "chdir" (string @-> returning int)
  let strerror = foreign "strerror" (int @-> returning string)
end
  
(** Here's one implementation of the FOREIGN signature:
    a module that provides the dynamic interpretation we've already seen *)
module Foreign_dynamic =
struct
  type 'a fn = 'a Ctypes.fn
  type 'a return = 'a
  type 'a result = 'a
  let (@->), returning = Foreign.((@->), returning)
  let foreign name typ = Foreign.foreign name typ
end

(** We can apply our parameterized binding module to the dynamic
   implementation...  *)
module X = My_functions(Foreign_dynamic);;

(** ... and call the bound functions immediately *)
X.puts "Hello, dynamic world"

(** Alternatively, we can apply other interpretations
    by passing the parameterized bindings module My_functions
    to some Ctypes functions that will supply suitable
    interpretations.

    First, the following call generates C stub code from My_functions *)
Cstubs.write_c Format.std_formatter ~prefix:"foo" (module My_functions);;

(** Next, the following call generates ML stub code from My_functions *)
Cstubs.write_ml Format.std_formatter ~prefix:"foo" (module My_functions);;

(** The generated code (which acts as another implementation of
   FOREIGN) can then be linked into the program and called *) 

(** Finally, here are some more interpretations.  We can indicate
    with the ~concurrency argument that we'd like the generated
    code to release OCaml's global run-time lock during each C call.

    Note the change in the generated C code.*)
Cstubs.write_c ~concurrency:Cstubs.unlocked Format.std_formatter ~prefix:"foo"
  (module My_functions);;

(** Or we can generate code that returns the value of the C global error
    flag 'errno' along with the return value of each function.

    Note the change in the type of the generated code to accommodate the
    additional returned value.
 *)
Cstubs.write_ml ~errno:Cstubs.return_errno Format.std_formatter ~prefix:"foo" (module My_functions);;

