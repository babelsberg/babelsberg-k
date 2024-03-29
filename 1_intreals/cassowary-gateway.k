require "builtins/builtins.k"
require "io/uris.k"

// This module currently realizes constraint construction
// TODO: move this out
module CASSOWARY-GATEWAY
  imports URIS
  imports BABELSBERG-CONSTRAINT-SYNTAX

  // getModel expresses the call to the solver in M ||= C
  syntax Constraint ::= "#getModel" "(" Constraint "," Int ")" [function]
	       | "#poll" "(" Int "," K ")" [function]
	       | "#checkResultOfRead" "(" Int "," TCPAnswer ")" [function]
	       | "#closeAndConvert" "(" Int "," String ")" [function]
  rule #getModel(C, Fd:Int) => #poll(Fd, #write(Fd, #printConstraints(C)))
  rule #poll(Fd:Int, _) => #checkResultOfRead(Fd, #read(Fd, 10000)) // try to read all
  rule #checkResultOfRead(Fd:Int, ReadResult:String) => #closeAndConvert(Fd, ReadResult)
  rule #checkResultOfRead(Fd:Int, #EOF) => #poll(Fd, .) // eof-case
  rule #closeAndConvert(Fd, ReadResult) => #parse(ReadResult, "Constraint")

  // helper rules to print sexps from the constraints
  syntax String ::= "#printConstraints" "(" Constraint ")" [function]
                  | "#printCExp" "(" Expression ")" [function]
  rule #printConstraints(.) => ""
  rule #printConstraints(Constraint1 && Constraint2)
       => #printConstraints(Constraint1) +String #printConstraints(Constraint2)
  rule #printConstraints(weak Constraint1)
       => "(weak " +String #printConstraints(Constraint1) +String ")\n"
  // AtomicConstraint
  rule #printConstraints(Expression1 = Expression2)
       => "(= " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")\n"
  rule #printConstraints(Expression1 >= Expression2)
       => "(>= " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")\n"
  rule #printConstraints(Expression1 <= Expression2)
       => "(<= " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")\n"
  // Expressions
  rule #printCExp(Expression1 / Expression2)
       => "(/ " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")"
  rule #printCExp(Expression1 * Expression2)
       => "(* " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")"
  rule #printCExp(Expression1 + Expression2)
       => "(+ " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")"
  rule #printCExp(Expression1 - Expression2)
       => "(- " +String #printCExp(Expression1) +String " " +String #printCExp(Expression2) +String ")"
  rule #printCExp(F:Float) => Float2String(F)
  rule #printCExp(X:Id) => Id2String(X)

  // XXX: found in records
  // rule #printCExp(X:Id >> L:Id) => Id2String(X) +String ">>" +String Id2String(L)
endmodule
