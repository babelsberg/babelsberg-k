require "builtins/builtins.k"
require "io/uris.k"

// This module currently realizes constraint construction
// TODO: move this out
module CASSOWARY-GATEWAY
  imports URIS
  imports BABELSBERG-CONSTRAINT-SYNTAX

  // getModel expresses the call to the solver in M ||= C
  syntax SConstraint ::= "#getModel" "(" SConstraint "," Int ")" [function]
	       | "#poll" "(" Int "," K ")" [function]
	       | "#checkResultOfRead" "(" Int "," TCPAnswer ")" [function]
	       | "#closeAndConvert" "(" Int "," String ")" [function]
  rule #getModel(C, Fd:Int) => #poll(Fd, #write(Fd, #printConstraints(C)))
  rule #poll(Fd:Int, _) => #checkResultOfRead(Fd, #read(Fd, 10000)) // try to read all
  rule #checkResultOfRead(Fd:Int, ReadResult:String) => #closeAndConvert(Fd, ReadResult)
  rule #checkResultOfRead(Fd:Int, #EOF) => #poll(Fd, .) // eof-case
  rule #closeAndConvert(Fd, ReadResult) => #parse(ReadResult, "SConstraint")

  // helper rules to print sexps from the constraints
  syntax String ::= "#printConstraints" "(" SConstraint ")" [function]
                  | "#printCExp" "(" SExpression ")" [function]
  rule #printConstraints(.) => ""
  rule #printConstraints(SConstraint1 [[&&]] SConstraint2)
       => #printConstraints(SConstraint1) +String #printConstraints(SConstraint2)
  rule #printConstraints([[weak]] SConstraint1)
       => "(weak " +String #printConstraints(SConstraint1) +String ")\n"
  // AtomicConstraint
  rule #printConstraints(SExpression1 [[=]] SExpression2)
       => "(= " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")\n"
  rule #printConstraints(SExpression1 [[>=]] SExpression2)
       => "(>= " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")\n"
  rule #printConstraints(SExpression1 [[<=]] SExpression2)
       => "(<= " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")\n"
  // Expressions
  rule #printCExp(SExpression1 [[/]] SExpression2)
       => "(/ " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")"
  rule #printCExp(SExpression1 [[*]] SExpression2)
       => "(* " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")"
  rule #printCExp(SExpression1 [[+]] SExpression2)
       => "(+ " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")"
  rule #printCExp(SExpression1 [[-]] SExpression2)
       => "(- " +String #printCExp(SExpression1) +String " " +String #printCExp(SExpression2) +String ")"
  rule #printCExp([[ F:Float ]]) => Float2String(F)
  rule #printCExp([[ X:Id ]]) => Id2String(X)
endmodule
