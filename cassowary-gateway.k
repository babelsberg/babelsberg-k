require "builtins/builtins.k"
require "io/uris.k"

// This module currently realizes constraint construction
// TODO: move this out
module CASSOWARY-GATEWAY
  imports URIS
  imports BABELSBERG-SYNTAX

  // getStays converts Map into stay constraints
  syntax Constraint ::= "#getStays" "(" Map ")" [function]
  	 	      | "weak" Constraint

  // getAssignments expresses E ||= C
  syntax Map ::= "#getAssignments" "(" Constraint "," Int ")" [function]
	       | "#poll" "(" Int "," K ")" [function]
	       | "#checkResultOfRead" "(" Int "," TCPAnswer ")" [function]
	       | "#closeAndConvert" "(" Int "," String ")" [function]
	       | "#convert" "(" K "," Constraint ")" [function]
	       | "#convertRest" "(" Map "," Constraint ")" [function]
  rule #getAssignments(C, Fd:Int) => #poll(Fd, #write(Fd, #printConstraints(C)))
  rule #poll(Fd:Int, _) => #checkResultOfRead(Fd, #read(Fd, 10000)) // try to read all
  rule #checkResultOfRead(Fd:Int, ReadResult:String) => #closeAndConvert(Fd, ReadResult)
  rule #checkResultOfRead(Fd:Int, #EOF) => #poll(Fd, .) // eof-case
  rule #closeAndConvert(Fd, ReadResult) => #convert(Fd, #parse(ReadResult, "Constraint"))
  rule #convert(_, Constraint) => #convertRest(.Map, Constraint)
  rule #convertRest(M, V = N && C) => #convertRest(M (V |-> N), C)
  rule #convertRest(M, V = N) => #convertRest(M (V |-> N), .)
  rule #convertRest(M, .) => M

  syntax String ::= "#printConstraints" "(" Constraint ")" [function]
                  | "#printCExp" "(" Expression ")" [function]
		  | "#printRecordEqual" "(" Expression "=" RecordExpression ")" [function]
  rule #printConstraints(.) => ""
  rule #printConstraints(Constraint1 && Constraint2)
       => #printConstraints(Constraint1) +String #printConstraints(Constraint2)
  rule #printConstraints(weak Constraint1)
       => "(weak " +String #printConstraints(Constraint1) +String ")\n"
  // AtomicConstraint
  rule #printConstraints(Expression1 = { RecordExpression })
       => #printRecordEqual(Expression1 = RecordExpression)
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
  rule #printCExp(I:Int) => Int2String(I)
  rule #printCExp(F:Float) => Float2String(F)
  rule #printCExp(X:Id) => Id2String(X)

  // construct record equality constraint
  rule #printRecordEqual(E1 = Label : E2)
       => "(= " +String #printCExp(E1) +String "_" +String Id2String(Label) +String " " +String #printCExp(E2) +String ")"
  rule #printRecordEqual(E1 = Label : E2 , RE)
       => "(= " +String #printCExp(E1) +String "_" +String Id2String(Label) +String " " +String #printCExp(E2) +String ")" +String #printRecordEqual(E1 = RE)

  rule #getStays((X |-> V) Rest) => (weak X = V) && #getStays(Rest) [function]
  rule #getStays(.) => .
endmodule
