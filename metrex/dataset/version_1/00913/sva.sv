// SVA for not_gate_using_nand
// Bind into DUT; checks function, internal NAND, and provides concise coverage.

module not_gate_sva(input logic in, input logic out, input logic nand_out);

  // Functional equivalence (4-state accurate, avoids race via ##0)
  property p_out_is_not_in;
    @(in or out) 1'b1 |-> ##0 (out === ~in);
  endproperty
  assert property (p_out_is_not_in);

  // Internal NAND implementation check
  property p_nand_correct;
    @(in or nand_out) 1'b1 |-> ##0 (nand_out === ~(in & in));
  endproperty
  assert property (p_nand_correct);

  // No spurious output changes (out only changes when in changes)
  property p_out_changes_only_with_in;
    @(out) 1'b1 |-> ##0 $changed(in);
  endproperty
  assert property (p_out_changes_only_with_in);

  // Coverage: truth table and both edges (including X propagation)
  cover property (@(in or out) (in === 1'b0) ##0 (out === 1'b1));
  cover property (@(in or out) (in === 1'b1) ##0 (out === 1'b0));
  cover property (@(in or out) (in === 1'bx) ##0 (out === 1'bx));
  cover property (@(posedge in) ##0 (out === 1'b0));
  cover property (@(negedge in) ##0 (out === 1'b1));

endmodule

// Bind SVA into the DUT (allows access to internal nand_out)
bind not_gate_using_nand not_gate_sva u_not_gate_sva (.in(in), .out(out), .nand_out(nand_out));