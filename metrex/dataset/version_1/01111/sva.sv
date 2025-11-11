// SVA checker for sky130_fd_sc_ms__a221oi
module a221oi_sva (
  input logic A1, A2, B1, B2, C1,
  input logic Y,
  input logic and0_out, and1_out, nor0_out_Y
);

  // Sample on any input edge; use ##0 to avoid delta races
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2 or
    posedge C1 or negedge C1
  ); endclocking

  // Gate-level decomposition must hold
  assert property (1'b1 |-> ##0 (and0_out   === (B1 & B2)));
  assert property (1'b1 |-> ##0 (and1_out   === (A1 & A2)));
  assert property (1'b1 |-> ##0 (nor0_out_Y === ~(and0_out | C1 | and1_out)));
  assert property (1'b1 |-> ##0 (Y          ===  nor0_out_Y));

  // End-to-end equivalence
  assert property (1'b1 |-> ##0 (Y === ~(C1 | (A1 & A2) | (B1 & B2))));

  // Dominance and consistency
  assert property (1'b1 |-> ##0 ((C1===1'b1)             |-> (Y===1'b0)));
  assert property (1'b1 |-> ##0 (((A1 & A2)===1'b1)      |-> (Y===1'b0)));
  assert property (1'b1 |-> ##0 (((B1 & B2)===1'b1)      |-> (Y===1'b0)));
  assert property (1'b1 |-> ##0 ((Y===1'b1) |-> (C1===1'b0 && (A1 & A2)===1'b0 && (B1 & B2)===1'b0)));
  assert property (1'b1 |-> ##0 ((Y===1'b0) |-> (C1===1'b1 || (A1 & A2)===1'b1 || (B1 & B2)===1'b1)));

  // No X/Z on outputs when inputs are known
  assert property (1'b1 |-> ##0 ((!$isunknown({A1,A2,B1,B2,C1})) |-> (!$isunknown({Y,and0_out,and1_out,nor0_out_Y))));

  // Toggle coverage
  cover property ($rose(A1)); cover property ($fell(A1));
  cover property ($rose(A2)); cover property ($fell(A2));
  cover property ($rose(B1)); cover property ($fell(B1));
  cover property ($rose(B2)); cover property ($fell(B2));
  cover property ($rose(C1)); cover property ($fell(C1));
  cover property ($rose(Y));  cover property ($fell(Y));

  // Functional corner coverage
  cover property (##0 (C1===1'b0 && (A1 & A2)===1'b0 && (B1 & B2)===1'b0 && Y===1'b1)); // Y=1 case
  cover property (##0 (C1===1'b1 && (A1 & A2)===1'b0 && (B1 & B2)===1'b0 && Y===1'b0)); // C1 term dominates
  cover property (##0 (C1===1'b0 && (A1 & A2)===1'b1 && (B1 & B2)===1'b0 && Y===1'b0)); // A-term dominates
  cover property (##0 (C1===1'b0 && (A1 & A2)===1'b0 && (B1 & B2)===1'b1 && Y===1'b0)); // B-term dominates
  cover property (##0 (C1===1'b1 && (A1 & A2)===1'b1 && (B1 & B2)===1'b1 && Y===1'b0)); // all terms high

endmodule

// Bind the checker into the DUT to access internal nets
bind sky130_fd_sc_ms__a221oi a221oi_sva sva_i (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .Y(Y),
  .and0_out(and0_out), .and1_out(and1_out), .nor0_out_Y(nor0_out_Y)
);