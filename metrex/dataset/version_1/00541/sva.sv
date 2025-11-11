// SVA for sky130_fd_sc_ls__a2bb2oi: Y = ~( (~(A1_N | A2_N)) | (B1 & B2) )
// Simplified: Y = (A1_N | A2_N) & (~B1 | ~B2)
module sky130_fd_sc_ls__a2bb2oi_sva (
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2,
  input logic Y
);

  // Sample on any input edge
  default clocking cb @(
    posedge A1_N or negedge A1_N or
    posedge A2_N or negedge A2_N or
    posedge B1   or negedge B1   or
    posedge B2   or negedge B2
  ); endclocking

  // Functional equivalence when inputs are known
  property p_func;
    !$isunknown({A1_N,A2_N,B1,B2}) |-> (! $isunknown(Y) &&
      (Y === ((A1_N | A2_N) & (~B1 | ~B2))));
  endproperty
  assert property (p_func);

  // Strong zero conditions (independent of the other input pair)
  property p_B_kill;
    (B1 === 1'b1 && B2 === 1'b1) |-> (Y === 1'b0);
  endproperty
  assert property (p_B_kill);

  property p_A_kill;
    (A1_N === 1'b0 && A2_N === 1'b0) |-> (Y === 1'b0);
  endproperty
  assert property (p_A_kill);

  // Strong one condition
  property p_Y_high;
    ((A1_N === 1'b1 || A2_N === 1'b1) &&
     (B1 === 1'b0  || B2 === 1'b0)) |-> (Y === 1'b1);
  endproperty
  assert property (p_Y_high);

  // Coverage: hit all quadrants and output toggle
  cover property (B1===1 && B2===1 && Y===0);                              // B kill
  cover property (A1_N===0 && A2_N===0 && Y===0);                          // A kill
  cover property ((A1_N===1 || A2_N===1) && (B1===0 || B2===0) && Y===1);  // Y=1 case
  cover property ((A1_N===0 && A2_N===0) && (B1===1 && B2===1) && Y===0);  // both kill
  cover property ($changed(Y));                                            // output toggles

endmodule

// Bind into DUT
bind sky130_fd_sc_ls__a2bb2oi sky130_fd_sc_ls__a2bb2oi_sva u_sva (
  .A1_N(A1_N), .A2_N(A2_N), .B1(B1), .B2(B2), .Y(Y)
);