require "./cassowary-gateway.k"

module BABELSBERG-INT-SYNTAX
  syntax Statement          ::= "skip"
                              | Variable ":=" Expression        [strict(2)]
                              | "always" Constraint
                              | Statement ";" Statement         [left]
			      | "unsat" | "unknown"

  syntax Constraint         ::= "True" | AtomicConstraint | "weak" AtomicConstraint
                              | Constraint "&&" Constraint [left]
                              | Constraint "||" Constraint [left] // TODO: fix this in the paper

  syntax AtomicConstraint   ::= Expression "<=" Expression [left]
                              | Expression ">=" Expression [left]
                              | Expression "=" Expression [left]

  syntax Expression         ::= Number | Variable
                              | Expression "/" Expression       [strict, left]
                              | Expression "*" Expression       [strict, left]
                              > Expression "+" Expression       [strict, left]
                              > Expression "-" Expression       [strict, left]

  syntax Number             ::= Float
  syntax Variable           ::= Id
  syntax Value              ::= Number | "fin"
endmodule

module BABELSBERG-CONSTRAINT-SYNTAX
  imports BABELSBERG-INT-SYNTAX // identical
endmodule

module BABELSBERG-INT
  imports BABELSBERG-INT-SYNTAX
  imports CASSOWARY-GATEWAY

  // tell K to stop evaluation when a Value is found
  syntax KResult            ::= Value

  // state
  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <C> . </C> // the current constraint system
    <Cassowary> #open("./cassowary-gateway.exchange"):Int </Cassowary>
  </T>

  // E-Num
  // realized by [strict] annotation above
  // E-Var
  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>
  // E-Op
  rule (F1:Float / F2:Float):Expression => F1 /Float F2
  rule (F1:Float * F2:Float):Expression => F1 *Float F2
  rule (F1:Float + F2:Float):Expression => F1 +Float F2
  rule (F1:Float - F2:Float):Expression => F1 -Float F2

  syntax K ::= "#mapTo(" K ")" [function]
  // ToNum
  rule #mapTo(Number) => Number
  // ToVar
  rule #mapTo(Variable) => Variable
  // ToArith
  rule #mapTo(E1 / E2) => #mapTo(E1) / #mapTo(E2)
  rule #mapTo(E1 * E2) => #mapTo(E1) * #mapTo(E2)
  rule #mapTo(E1 + E2) => #mapTo(E1) + #mapTo(E2)
  rule #mapTo(E1 - E2) => #mapTo(E1) - #mapTo(E2)
  // ToCompare
  rule #mapTo(E1 = E2) => #mapTo(E1) = #mapTo(E2)
  rule #mapTo(E1 <= E2) => #mapTo(E1) <= #mapTo(E2)
  rule #mapTo(E1 >= E2) => #mapTo(E1) >= #mapTo(E2)
  // ToTrue
  rule #mapTo(True:Constraint) => 1.0 = 1.0
  // ToCombine
  rule #mapTo(C1 || C2) => #mapTo(C1) || #mapTo(C2)
  rule #mapTo(C1 && C2) => #mapTo(C1) && #mapTo(C2)
  // ToWeak
  rule #mapTo(weak C) => weak #mapTo(C)

  syntax Map ::= "#mapFrom" "(" Map "," Constraint ")" [function]
  // FromEmpty
  rule #mapFrom(M, .) => M
  // FromOne
  rule #mapFrom(M, V:Variable = N && C) => #mapFrom(M (V |-> N), C)
  rule #mapFrom(M, C:AtomicConstraint) => #mapFrom(M, C && .)

  syntax K ::= "#solve" "(" Constraint ")" [function]
             | "#solved" "(" Constraint ")" [function]
	     | "||=" "(" Map ")"
	     | "/||="
	     | "?||="
  // getModel (represent call to the solver)
  rule <k> #solve(C) => #solved(#getModel(#mapTo(C), Fd)) ...</k> <Cassowary> Fd </Cassowary>

  // Unsat
  rule #solved(1.0 = 2.0) => /||=
  // Unknown
  rule #solved(0.0 = 1.0) => ?||=

  // Solve
  rule #solved(Ec) => ||=(#mapFrom(., Ec))

  syntax AtomicConstraint ::= "#stay" "(" Map ")" [function]
  // StayEmpty
  rule #stay(.) => .
  // StayOne
  rule #stay((X |-> V) E0:Map) => (weak X = V) && #stay(E0)

  // S-Asgn
  rule <k> X := V:Expression => #solve(C && X = V && #stay(E)) ~> X := V ...</k> <E> E </E> <C> C </C>
  rule <k> ||=(Ec) ~> X := V => skip ...</k> <E> _ => Ec </E>
  // S-AsgnUnsat
  rule <k> /||= ~> X := V => unsat ...</k>
  // S-AsgnUnknown
  rule <k> ?||= ~> X := V => unknown ...</k>

  // S-Always
  rule <k> always C0 => #solve(C && C0 && #stay(E)) ~> always C && C0 ...</k> <E> E </E> <C> C </C>
  rule <k> ||=(Ec) ~> always C => skip ...</k> <E> _ => Ec </E> <C> _ => C </C>
  // S-AlwaysUnsat
  rule <k> /||= ~> always C => unsat ...</k>
  // S-AlwaysUnknown
  rule <k> ?||= ~> always C => unknown ...</k>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]
  rule .K => fin
  // S-SeqSkip
  rule skip ~> S2 => S2 [structural]
  // S-SeqUnsat
  // rule unsat ~> _  => unsat [structural]
  // S-SeqUnknown
  // rule unknown ~> _  => unsat [structural]
endmodule
