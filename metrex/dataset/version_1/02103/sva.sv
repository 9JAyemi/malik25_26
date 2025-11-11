// SVA for sky130_fd_sc_hdll__nand3
// Bind into the DUT; checks truth table (incl. X/Z semantics), buffer passthrough, rails, and covers key cases.

module sky130_fd_sc_hdll__nand3_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB,
  input logic nand0_out_Y
);

  // Trigger checks on any input edge
  default clocking cb @ (posedge A or negedge A or
                         posedge B or negedge B or
                         posedge C or negedge C); endclocking

  // Functional equivalence (4-state): Y must equal ~(A & B & C)
  property p_func; 1'b1 |-> ##0 (Y === ~(A & B & C)); endproperty
  assert property (cb p_func);

  // Buffer integrity: Y must equal internal nand output
  property p_buf_passthru; 1'b1 |-> ##0 (Y === nand0_out_Y); endproperty
  assert property (cb p_buf_passthru);

  // Deterministic cases: any 0 forces Y=1; all 1's force Y=0
  assert property (cb (A===1'b0 || B===1'b0 || C===1'b0) |-> ##0 (Y===1'b1));
  assert property (cb (A===1'b1 && B===1'b1 && C===1'b1) |-> ##0 (Y===1'b0));

  // X-propagation: with no zeros and at least one X/Z on inputs, Y must be unknown
  assert property (cb !(A===1'b0 || B===1'b0 || C===1'b0) && $isunknown({A,B,C})
                       |-> ##0 $isunknown(Y));

  // Output must never be high-impedance
  assert property (cb 1'b1 |-> ##0 (Y !== 1'bz));

  // Rails (should be constant in this cell)
  assert property (cb 1'b1 |-> ##0 (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0));

  // Functional coverage: all 8 input combinations with expected Y
  cover property (cb (A===0 && B===0 && C===0 && Y===1));
  cover property (cb (A===0 && B===0 && C===1 && Y===1));
  cover property (cb (A===0 && B===1 && C===0 && Y===1));
  cover property (cb (A===0 && B===1 && C===1 && Y===1));
  cover property (cb (A===1 && B===0 && C===0 && Y===1));
  cover property (cb (A===1 && B===0 && C===1 && Y===1));
  cover property (cb (A===1 && B===1 && C===0 && Y===1));
  cover property (cb (A===1 && B===1 && C===1 && Y===0));

  // Coverage: unknown-case exercised
  cover property (cb !(A===0 || B===0 || C===0) && $isunknown({A,B,C}) && $isunknown(Y));

  // Y toggle coverage
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

endmodule

bind sky130_fd_sc_hdll__nand3 sky130_fd_sc_hdll__nand3_sva nand3_sva_i (.*);