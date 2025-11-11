// SVA for sky130_fd_sc_hd__o31a: X = (A1 | A2 | A3) & B1
// Bind this module to the DUT instance(s).

module sky130_fd_sc_hd__o31a_sva (
  input logic A1, A2, A3, B1, X,
  input logic or0_out, and0_out_X,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any relevant combinational activity
  default clocking cb @(A1 or A2 or A3 or B1 or X or or0_out or and0_out_X); endclocking

  // Power pins must be correct constants
  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
    else $error("o31a: power pins not at expected constants");

  // Internal structure correctness
  assert property (or0_out    === (A1 | A2 | A3))
    else $error("o31a: OR stage mismatch");
  assert property (and0_out_X === (or0_out & B1))
    else $error("o31a: AND stage mismatch");
  assert property (X          === and0_out_X)
    else $error("o31a: BUF stage mismatch");

  // End-to-end functional equivalence
  assert property (X === ((A1 | A2 | A3) & B1))
    else $error("o31a: functional mismatch");

  // Useful implications and X-propagation sanity
  assert property ((B1===1'b0) |-> (X===1'b0))
    else $error("o31a: B1=0 must force X=0");
  assert property (((A1!==1'bx) && (A2!==1'bx) && (A3!==1'bx) && (B1!==1'bx)) |-> (X!==1'bx))
    else $error("o31a: X unknown with all inputs known");

  // Coverage: value coverage and transitions
  cover property (B1 && (A1||A2||A3) && (X===1'b1));
  cover property ((!B1) && (X===1'b0));
  cover property ($rose(X));
  cover property ($fell(X));

  // Compact full input-space coverage and cross with X
  covergroup cg_o31a @(A1 or A2 or A3 or B1);
    coverpoint {A1,A2,A3,B1} { bins all[] = {[0:15]}; }
    coverpoint X { bins zero = {1'b0}; bins one = {1'b1}; bins unk = {1'bx}; }
    cross {A1,A2,A3,B1}, X;
  endgroup
  cg_o31a cg = new();

endmodule

// Bind into the DUT (connects to internal nets for structural checks)
bind sky130_fd_sc_hd__o31a sky130_fd_sc_hd__o31a_sva o31a_sva_i (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1), .X(X),
  .or0_out(or0_out), .and0_out_X(and0_out_X),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);