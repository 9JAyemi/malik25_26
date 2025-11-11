// SVA for sky130_fd_sc_ls__and2b
// Checks function X = (~A_N) & B, stage-by-stage correctness, rail sanity, and covers truth table and toggles.

`ifndef SKY130_FD_SC_LS__AND2B_SVA
`define SKY130_FD_SC_LS__AND2B_SVA

module sky130_fd_sc_ls__and2b_sva (
  input logic X, A_N, B,
  input logic not0_out, and0_out_X,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any relevant edge (inputs or output)
  default clocking cb @(
    posedge A_N or negedge A_N or
    posedge B   or negedge B   or
    posedge X   or negedge X
  ); endclocking

  // Power/ground rails constant
  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Functional equivalence when inputs are known
  assert property ((A_N inside {0,1} && B inside {0,1})
                   |-> ##0 (X inside {0,1} && X == ((~A_N) & B)));

  // Stage-by-stage structural checks
  assert property ((A_N inside {0,1})
                   |-> ##0 (not0_out inside {0,1} && not0_out == ~A_N));

  assert property (((not0_out inside {0,1}) && (B inside {0,1}))
                   |-> ##0 (and0_out_X inside {0,1} && and0_out_X == (not0_out & B)));

  assert property ((and0_out_X inside {0,1})
                   |-> ##0 (X inside {0,1} && X == and0_out_X));

  // Output edge cause (no spurious toggles)
  assert property ($rose(X) |-> (B==1'b1 && A_N==1'b0));
  assert property ($fell(X) |-> (B==1'b0 || A_N==1'b1));

  // Truth-table coverage (all 4 input combos with expected X)
  cover property (A_N==1'b0 && B==1'b1 && X==1'b1);
  cover property (A_N==1'b0 && B==1'b0 && X==1'b0);
  cover property (A_N==1'b1 && B==1'b1 && X==1'b0);
  cover property (A_N==1'b1 && B==1'b0 && X==1'b0);

  // Toggle coverage
  cover property ($rose(X));
  cover property ($fell(X));
  cover property ($rose(not0_out));
  cover property ($fell(not0_out));
  cover property ($rose(and0_out_X));
  cover property ($fell(and0_out_X));

endmodule

// Bind into DUT; internal nets are referenced by name
bind sky130_fd_sc_ls__and2b sky130_fd_sc_ls__and2b_sva u_and2b_sva (
  .X(X), .A_N(A_N), .B(B),
  .not0_out(not0_out), .and0_out_X(and0_out_X),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);

`endif