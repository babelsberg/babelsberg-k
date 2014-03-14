#!/usr/bin/env ruby
require "bundler/setup"
require "cassowary"

variables = {}

class SexpSolver
  include Cassowary
  attr_reader :variables

  def initialize(variables)
    @variables = variables
  end

  def parse_and_solve(str)
    sexp = str.strip
    whitespace = " \n\r\t"
    atom_end = whitespace + "()"

    constraints = []
    stack, atom, i, length = [], [], 0, sexp.size
    while i < length do
      c = sexp[i]
      reading_tuple = atom.size > 0
      unless reading_tuple
        if c == '('
          stack << []
        elsif c == ')'
          pred = stack.size - 2
          if pred >= 0
            stack[pred] << self.evaluate_sexpr(stack.pop())
          else
            constraints << self.evaluate_sexpr(stack.pop())
          end
        elsif whitespace.include? c
        else
          atom << c
        end
      else
        if atom_end.include? c
          stack[-1] << atom.join
          atom = []
          next
        else
          atom << c
        end
      end
      i += 1
    end

    solver = SimplexSolver.new
    constraints.each do |cn|
      solver.add_constraint cn
    end
  end

  OpMapping = {"=" => :cn_equal, "<=" => :cn_leq, ">=" => :cn_geq,
               "+" => :+, "-" => :-, "*" => :*, "/" => :/,
               "weak" => :weak}
  def evaluate_sexpr(l)
    op = OpMapping[l[0]]
    args = l[1..-1].map do |i|
      if i.is_a? String
        begin
          Float(i)
        rescue ArgumentError
          variables[i] ||= Variable.new(name: i)
        end
      else
        i
      end
    end
    args[0].send(op, *args[1..-1])
  end

  class ::Cassowary::LinearEquation
    def weak
      self.strength = ::Cassowary::Strength::WeakStrength
      self
    end
  end
end

FPath = "./cassowary-gateway.exchange"
file = File.open(FPath, 'r+')
at_exit do
  File.unlink FPath
end

loop do
  while !input = file.read(100000)
    sleep 0.1
  end
  begin
    SexpSolver.new(variables).parse_and_solve(input)
    puts variables
    file << variables.values.map do |v|
      "#{v.name} = #{v.value}"
    end.join(" && ") << "\n\n"
  rescue Cassowary::RequiredFailure
    file << "-1 = -2\n\n"
    exit
  end
end
