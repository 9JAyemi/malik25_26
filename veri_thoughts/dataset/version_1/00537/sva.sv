// SVA for three_input_full_adder
module three_input_full_adder_sva (
  input logic A, B, C,
  input logic S, Cout,
  input logic n1, n2, n3
);

  // After any primary input change, logic must settle in the same timestep (##0)
  // and match both the gate decomposition and the canonical full-adder equations.
  property p_functional_correctness;
    ($changed({A,B,C}) && !$isunknown({A,B,C}))
    |-> ##0
       ( !$isunknown({n1,n2,n3,S,Cout})
         && (n1 == (A ^ B))
         && (n2 == (A & B))
         && (n3 == (n1 & C))
         && (S  == (n1 ^ C))
         && (S  == (A ^ B ^ C))
         && (Cout == (n2 | n3))
         && (Cout == ((A & B) | (B & C) | (A & C)))
       );
  endproperty
  a_functional_correctness: assert property (@(*) p_functional_correctness);

  // Truth-table coverage (inputs known)
  cover property (@(*) (! $isunknown({A,B,C})) && !A && !B && !C && !S && !Cout);
  cover property (@(*) (! $isunknown({A,B,C})) && !A && !B &&  C &&  S && !Cout);
  cover property (@(*) (! $isunknown({A,B,C})) && !A &&  B && !C &&  S && !Cout);
  cover property (@(*) (! $isunknown({A,B,C})) && !A &&  B &&  C && !S &&  Cout);
  cover property (@(*) (! $isunknown({A,B,C})) &&  A && !B && !C &&  S && !Cout);
  cover property (@(*) (! $isunknown({A,B,C})) &&  A && !B &&  C && !S &&  Cout);
  cover property (@(*) (! $isunknown({A,B,C})) &&  A &&  B && !C && !S &&  Cout);
  cover property (@(*) (! $isunknown({A,B,C})) &&  A &&  B &&  C &&  S &&  Cout);

endmodule

// Bind into the DUT (accesses internal nets n1/n2/n3)
bind three_input_full_adder three_input_full_adder_sva sva_i (
  .A(A), .B(B), .C(C), .S(S), .Cout(Cout), .n1(n1), .n2(n2), .n3(n3)
);