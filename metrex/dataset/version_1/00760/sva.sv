// SVA bind module for four_input_module
module four_input_module_sva (
  input logic A1, A2, A3, B1,
  input logic Y
);

  // Sample on any input edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1
  ); endclocking

  // Functional equivalence (simplified): Y == (~B1) | (A1&A2&A3)
  assert property ( Y === ((~B1) | (A1 & A2 & A3)) )
    else $error("Y mismatch: Y=%0b A1=%0b A2=%0b A3=%0b B1=%0b", Y, A1, A2, A3, B1);

  // Deterministic cases (4-state strong checks)
  assert property ( (B1 === 1'b0) |-> (Y === 1'b1) )
    else $error("B1=0 must force Y=1");
  assert property ( (B1 === 1'b1) && (A1===1'b1) && (A2===1'b1) && (A3===1'b1) |-> (Y === 1'b1) )
    else $error("B1=1 and all A's=1 must yield Y=1");
  assert property ( (B1 === 1'b1) && !(A1 && A2 && A3) |-> (Y === 1'b0) )
    else $error("B1=1 and not all A's=1 must yield Y=0");

  // Functional coverage: all result-determining scenarios
  cover property ( (B1==1'b0) && (Y==1'b1) );                         // Y forced high by B1=0
  cover property ( (B1==1'b1) && A1 && A2 && A3 && (Y==1'b1) );       // Y high via A1&A2&A3
  cover property ( (B1==1'b1) && !(A1&&A2&&A3) && (Y==1'b0) );        // Y low when any A=0 with B1=1

  // Output transition coverage
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

endmodule

// Bind into the DUT
bind four_input_module four_input_module_sva sva_u (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .Y(Y)
);