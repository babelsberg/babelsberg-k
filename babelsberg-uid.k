require "./cassowary-gateway.k"

module BABELSBERG-UID-SYNTAX
  syntax Statement          ::= "skip"
                              | Variable ":=" Expression        [strict(2)]
			      | Variable "." Label ":=" Expression [strict(2 3)]
			      | Variable ":=" "new" "{" RecordExpression "}"
                              | "always" Constraint
                              | "weak" "always" Constraint
                              | Statement ";" Statement         [left]
			      | "unsat"

  syntax Expression         ::= Number | Variable
                              | Expression "/" Expression       [strict, left]
                              | Expression "*" Expression       [strict, left]
                              > Expression "+" Expression       [strict, left]
                              > Expression "-" Expression       [strict, left]
			      | Expression "." Label
			      | Reference

  syntax ArithmeticConstraint ::= Expression "<=" Expression
                                | Expression ">=" Expression
                                | Expression "=" Expression

  syntax Constraint         ::= AtomicConstraint
                              > Constraint "&&" Constraint      [left]

  syntax Number             ::= Int | Float  // a builtin
  syntax Variable           ::= Id           // a builtin

  // TODO: do we need Operator?
  syntax Operator	    ::= "+" | "-" | "*" | "/" | "=" | ">=" | "<="
  syntax Label              ::= Id
  syntax Value              ::= Bool | Number | Reference | Constraint

  // Helper
  syntax RecordExpression ::= Label ":" Expression                  [strict(2)]
                            | RecordExpression "," RecordExpression [left, seqstrict]
endmodule

module BABELSBERG-UID
  imports CASSOWARY-GATEWAY

  syntax KResult            ::= Value

  configuration <T>
    <k> $PGM:Statement </k> // the remaining program
    <E> .Map </E> // the environment
    <E> .Map </E> // the heap
    <C> . </C> // the current constraint system
    <Cassowary> #open("./cassowary-gateway.exchange"):Int </Cassowary>
  </T>

  // E-Var
  rule <k> X:Variable => V ...</k> <E>... X |-> V ...</E>

  // E-Op
  rule (I1:Int / I2:Int):Expression => I1 /Int I2
  rule (I1:Int * I2:Int):Expression => I1 *Int I2
  rule (I1:Int + I2:Int):Expression => I1 +Int I2
  rule (I1:Int - I2:Int):Expression => I1 -Int I2
  rule (F1:Float / F2:Float):Expression => F1 /Float F2
  rule (F1:Float * F2:Float):Expression => F1 *Float F2
  rule (F1:Float + F2:Float):Expression => F1 +Float F2
  rule (F1:Float - F2:Float):Expression => F1 -Float F2

  // E-Field
  rule ({ L : V, A } . L) => V
  rule ({ B, L : V, A } . L) => V
  rule ({ B, L : V } . L) => V


  // S-Unsat
  // TODO... this should really be in the S-Asgn and S-Always rules
  rule <k>_ => unsat</k> <E> (-1 |-> -2) => .Map </E>

  syntax K ::= "checkSat" "(" Map "," Constraint ")"
  // S-Asgn
  rule <k> X := V:Expression => checkSat(#getAssignments(C && X = V && #getStays(E) && #getStays(H), Fd), C) ...</k>
       <E> E </E> <C> C </C> <Cassowary> Fd </Cassowary>

  // S-AsgnField
  rule <k> X.L := V:Expression => checkSat(#getAssignments(C && X.L = V && #getStays(E) && #getStays(H), Fd), C) ...</k>
       <E> E </E> <C> C </C> <Cassowary> Fd </Cassowary>

  // S-AsgnNew
  // TODO

  // S-Always
  rule <k> always C0:Constraint => checkSat(#getAssignments(C && C0 && #getStays(E) && #getStays(H), Fd), C && C0) ...</k>
       <E> E </E> <C> C </C> <Cassowary> Fd </Cassowary>

  // S-unsat -- Hack, we're using an invalid mapping (-1 -> -2) as marker for unsat
  rule <k> checkSat((-1 |-> -2), C) ~> _ => unsat </k>
  // S-sat
  rule <k> checkSat(E, C) => . ...</k> <E> _ => E </E> <C> _ => C </C>

  // S-SeqStep
  rule S1 ; S2 => S1 ~> S2 [structural]
endmodule
