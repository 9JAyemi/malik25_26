module three_input_gate_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic Y
);

  // Functional equivalence when inputs are known
  assert property ( (!$isunknown({A1,A2,B1})) |-> (Y == ((A1 & A2) | B1)) )
    else $error("three_input_gate: Y != (A1&A2)|B1 when inputs are known");

  // Output must be known whenever inputs are known
  assert property ( (!$isunknown({A1,A2,B1})) |-> (!$isunknown(Y)) )
    else $error("three_input_gate: Y is X/Z while inputs are 0/1");

  // Useful decomposed checks (concise dominance/debug)
  assert property ( (B1 == 1'b1) |-> (Y == 1'b1) )
    else $error("three_input_gate: B1=1 must force Y=1");
  assert property ( (B1 == 1'b0) |-> (Y == (A1 & A2)) )
    else $error("three_input_gate: B1=0 => Y must equal A1&A2");

  // Functional coverage: all 8 input combinations with correct Y
  cover property ( {A1,A2,B1} == 3'b000 && Y==1'b0 );
  cover property ( {A1,A2,B1} == 3'b001 && Y==1'b1 );
  cover property ( {A1,A2,B1} == 3'b010 && Y==1'b0 );
  cover property ( {A1,A2,B1} == 3'b011 && Y==1'b1 );
  cover property ( {A1,A2,B1} == 3'b100 && Y==1'b0 );
  cover property ( {A1,A2,B1} == 3'b101 && Y==1'b1 );
  cover property ( {A1,A2,B1} == 3'b110 && Y==1'b1 );
  cover property ( {A1,A2,B1} == 3'b111 && Y==1'b1 );

  // Output toggling seen
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

endmodule

// Bind into DUT
bind three_input_gate three_input_gate_sva u_three_input_gate_sva (
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .Y(Y)
);