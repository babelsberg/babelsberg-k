require "builtins/builtins.k"
require "io/uris.k"

module BABELSBERG-CONSTRAINT-SYNTAX
  syntax AtomicConstraint   ::= CExpression "<=" CExpression
                              | CExpression ">=" CExpression
                              | CExpression "=" CExpression

  syntax Constraint         ::= AtomicConstraint
                              > Constraint "&&" Constraint      [left]

  syntax CExpression        ::= Number | Variable
                              | CExpression "/" CExpression     [left]
                              | CExpression "*" CExpression     [left]
                              > CExpression "+" CExpression     [left]
                              > CExpression "-" CExpression     [left]
endmodule

module BABELSBERG
  imports URIS
  imports BABELSBERG-CONSTRAINT-SYNTAX

  // getModel expresses E ||= C
  // it gets stuck if no model is available, so we don't need an explicit "unsat" case
  syntax Map ::= "#getModel" "(" Constraint "," String ")" [function]
               | "#writeAndPoll" "(" Constraint "," Int ")" [function]
	       | "#poll" "(" Int "," K ")" [function]
	       | "#checkResultOfRead" "(" Int "," TCPAnswer ")" [function]
	       | "#closeAndConvert" "(" Int "," String ")" [function]
	       | "#convert" "(" K "," Constraint ")" [function]
	       | "#convertRest" "(" Map "," Constraint ")" [function]
  rule #getModel(C, Path) => #writeAndPoll(C, #open(Path))
  rule #writeAndPoll(C, Fd) => #poll(Fd, #write(Fd, #printConstraints(C)))
  rule #poll(Fd:Int, _) => #checkResultOfRead(Fd, #read(Fd, 10000)) // try to read all
  rule #checkResultOfRead(Fd:Int, ReadResult:String) => #closeAndConvert(Fd, ReadResult)
  rule #checkResultOfRead(Fd:Int, _) => #poll(Fd, .) // eof-case
  rule #closeAndConvert(Fd, ReadResult) => #convert(#close(Fd), #parse(ReadResult, "Constraint"))
  rule #convert(_, Constraint) => #convertRest(.Map, Constraint)
  rule #convertRest(M, V = N && C) => #convertRest(M (V |-> N), C)
  rule #convertRest(M, V = N) => #convertRest(M (V |-> N), .)
  rule #convertRest(M, .) => M

  syntax String ::= "#printConstraints" "(" Constraint ")" [function]
                  | "#printCExp" "(" CExpression ")" [function]
  rule #printConstraints(.) => ""
  rule #printConstraints(Constraint1 && Constraint2)
       => #printConstraints(Constraint1) +String #printConstraints(Constraint2)
  // AtomicConstraint
  rule #printConstraints(CExpression1 = CExpression2)
       => "(= " +String #printCExp(CExpression1) +String #printCExp(CExpression2) +String ")\n"
  rule #printConstraints(CExpression1 >= CExpression2)
       => "(>= " +String #printCExp(CExpression1) +String #printCExp(CExpression2) +String ")\n"
  rule #printConstraints(CExpression1 <= CExpression2)
       => "(<= " +String #printCExp(CExpression1) +String #printCExp(CExpression2) +String ")\n"
  // CExpressions
  rule #printCExp(CExpression1 / CExpression2)
       => "(/ " +String #printCExp(CExpression1) +String " " +String #printCExp(CExpression2) +String ")"
  rule #printCExp(CExpression1 * CExpression2)
       => "(* " +String #printCExp(CExpression1) +String " " +String #printCExp(CExpression2) +String ")"
  rule #printCExp(CExpression1 + CExpression2)
       => "(+ " +String #printCExp(CExpression1) +String " " +String #printCExp(CExpression2) +String ")"
  rule #printCExp(CExpression1 - CExpression2)
       => "(- " +String #printCExp(CExpression1) +String " " +String #printCExp(CExpression2) +String ")"
  rule #printCExp(I:Int) => Int2String(I)
  rule #printCExp(F:Float) => Float2String(F)
  rule #printCExp(X:Id) => Id2String(X)

  // getStays converts Map into stay constraints
  syntax Constraint ::= "#getStays" "(" Map ")" [function]
  rule #getStays((X |-> V) Rest) => X = V && #getStays(Rest) [function]
  rule #getStays(.) => .
endmodule
