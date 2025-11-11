// SVA for three_input_gate: Y = B1 | (A1 & A2)
module three_input_gate_sva (
  input logic A1, A2, B1, Y,
  input logic A1_AND_A2, B1_OR_A1_AND_A2
);

  // Clocking on any input edge; use ##0 to avoid preponed-region races
  clocking cb @ (posedge A1 or negedge A1 or
                 posedge A2 or negedge A2 or
                 posedge B1 or negedge B1);
  endclocking
  default clocking cb;

  // Functional equivalence and X-prop
  assert property ( !$isunknown({A1,A2,B1}) |-> ##0 (Y == (B1 | (A1 & A2))) )
    else $error("Y != B1 | (A1 & A2)");
  assert property ( !$isunknown({A1,A2,B1}) |-> ##0 !$isunknown(Y) )
    else $error("Y went X/Z with fully-known inputs");
  assert property ( B1 |-> ##0 Y )  // B1=1 forces Y=1
    else $error("B1=1 did not force Y=1");
  assert property ( (B1==0 && !$isunknown({A1,A2})) |-> ##0 (Y == (A1 & A2)) )
    else $error("B1=0 path incorrect");

  // Structural consistency of internal nets
  assert property ( ##0 (A1_AND_A2 === (A1 & A2)) )
    else $error("A1_AND_A2 mismatch");
  assert property ( ##0 (B1_OR_A1_AND_A2 === (B1 | A1_AND_A2)) )
    else $error("B1_OR_A1_AND_A2 mismatch");
  assert property ( ##0 (Y === B1_OR_A1_AND_A2) )
    else $error("Y != B1_OR_A1_AND_A2");

  // Truth-table coverage (all 8 input combinations with expected Y)
  cover property ( (A1==0 && A2==0 && B1==0) |-> ##0 (Y==0) );
  cover property ( (A1==0 && A2==1 && B1==0) |-> ##0 (Y==0) );
  cover property ( (A1==1 && A2==0 && B1==0) |-> ##0 (Y==0) );
  cover property ( (A1==1 && A2==1 && B1==0) |-> ##0 (Y==1) );
  cover property ( (A1==0 && A2==0 && B1==1) |-> ##0 (Y==1) );
  cover property ( (A1==0 && A2==1 && B1==1) |-> ##0 (Y==1) );
  cover property ( (A1==1 && A2==0 && B1==1) |-> ##0 (Y==1) );
  cover property ( (A1==1 && A2==1 && B1==1) |-> ##0 (Y==1) );

  // Toggle coverage
  cover property ( $rose(A1) );  cover property ( $fell(A1) );
  cover property ( $rose(A2) );  cover property ( $fell(A2) );
  cover property ( $rose(B1) );  cover property ( $fell(B1) );
  cover property ( $rose(Y) );   cover property ( $fell(Y) );

endmodule

// Bind into DUT (connects to internal nets as well)
bind three_input_gate three_input_gate_sva sva_i (
  .A1(A1), .A2(A2), .B1(B1), .Y(Y),
  .A1_AND_A2(A1_AND_A2), .B1_OR_A1_AND_A2(B1_OR_A1_AND_A2)
);