// SVA checker for sky130_fd_sc_hd__o21bai
// Function: Y = B1_N | (~A1 & ~A2) = ~(~B1_N & (A1 | A2))
// Includes structural checks, functional equivalence, X-prop, and full input-space coverage.

module sky130_fd_sc_hd__o21bai_sva (
  input logic Y,
  input logic A1,
  input logic A2,
  input logic B1_N,
  // internal nets from DUT (for structural checks)
  input logic b,
  input logic or0_out,
  input logic nand0_out_Y
);

  // Sample on any edge of relevant signals
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1_N or negedge B1_N or
    posedge Y or negedge Y or
    posedge b or negedge b or
    posedge or0_out or negedge or0_out or
    posedge nand0_out_Y or negedge nand0_out_Y
  ); endclocking

  // Structural net checks
  assert property (b === ~B1_N);
  assert property (or0_out === (A1 | A2));
  assert property (nand0_out_Y === ~(b & or0_out));
  assert property (Y === nand0_out_Y);

  // Functional equivalence (simplified boolean form)
  assert property (Y === (B1_N | (~A1 & ~A2)));

  // Behavioral corner cases
  assert property ((B1_N === 1'b1) |-> (Y === 1'b1)); // B1_N dominates high
  assert property (((B1_N === 1'b0) && (A1 === 1'b1 || A2 === 1'b1)) |-> (Y === 1'b0));
  assert property (((A1 === 1'b0) && (A2 === 1'b0)) |-> (Y === B1_N));

  // No X/Z on Y when inputs are known
  assert property ((!$isunknown({A1,A2,B1_N})) |-> (!$isunknown(Y)));

  // Full input-space functional coverage (8 combos)
  cover property (A1===1'b0 && A2===1'b0 && B1_N===1'b0 && Y===1'b1);
  cover property (A1===1'b0 && A2===1'b0 && B1_N===1'b1 && Y===1'b1);
  cover property (A1===1'b0 && A2===1'b1 && B1_N===1'b0 && Y===1'b0);
  cover property (A1===1'b0 && A2===1'b1 && B1_N===1'b1 && Y===1'b1);
  cover property (A1===1'b1 && A2===1'b0 && B1_N===1'b0 && Y===1'b0);
  cover property (A1===1'b1 && A2===1'b0 && B1_N===1'b1 && Y===1'b1);
  cover property (A1===1'b1 && A2===1'b1 && B1_N===1'b0 && Y===1'b0);
  cover property (A1===1'b1 && A2===1'b1 && B1_N===1'b1 && Y===1'b1);

  // Output toggle coverage
  cover property ($rose(Y));
  cover property ($fell(Y));

endmodule

// Bind into the DUT to access both ports and internal nets by name
bind sky130_fd_sc_hd__o21bai sky130_fd_sc_hd__o21bai_sva
  o21bai_sva_i (.*);