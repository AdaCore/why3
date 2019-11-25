External printer for task/arguments parser for transformations
==============================================================

* Operators are printed the Ada way:

| Why3 | Ada        |
|------|------------|
| `<>` | `/=`       |
| `/\` | `and`      |
| `\/` | `or`       |
| `&&` | `and then` |
| `||` | `or else`  |

* Attributes are printed and can be used:
  Functions with attribute `name` (could be `syntax`) as `First` or `Last` are
  printed as attributes:

| Why3      | Ada       |
|:----------|----------:|
| `first A` | `A'First` |
| `last A`  | `A'Last`  |

* When the type is detected to be a Why3 record type: fields are printed in dot
  notation: X.Y.Z
  Also, parsed the same way for argument of transformations

* Quantifiers are printed in a close way to Ada:

| Why3            | Ada                  |
|-----------------|----------------------|
| `forall x.`     | `for all x => `      |
| `exists x.`     | `for some x => `     |
| `forall x:int.` | `for all x:int => `  |
| `exists x:int.` | `for some x:int => ` |

* Notation for Ada-like intervals for quantification:
| Why3                               | Ada                        |
|------------------------------------|----------------------------|
| `forall x. x <= y and y <= z -> P` | `for all x in y .. z => P` |

* Ada arrays are recognized by the tool with attributes on the type and on the
  getter functions such as:

  `type __t [@syntax:array:elts] = { elts [@syntax:getter:elts] : int -> int; foo: bar}`

  `function get [@syntax:getter:get] (a: __t) (i: int) : int = a.elts i`

  This allows `elts` to be directly understood as an array access:

| Why3       | Ada    |
|------------|--------|
| `get A I`  | `A(I)` |
| `elts A I` | `A(I)` |


  When parsing, `elts` is used as the default getter.


* Record type definitions are printed à la Ada:
| Why3                         | Ada                 |
|------------------------------|---------------------|
| `type t = { F: r; G : bool}` | `type t is`         |
|                              | `  record  -- t'mk` |
|                              | `     F: r`         |
|                              | `     g: bool`      |
|                              | `  end record`      |


* Bitvector/ <range 0 256> types/constant are printed with an Ada name:

| Why3                               | Ada                      |
|------------------------------------|--------------------------|
| `type t [@name:M] = <range 0 256>` | `type M = <range 0 256>` |
| `(22:t)`                           | `(22:M)`                 |
