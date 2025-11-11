// SVA for top_module
// Bind-in module; accesses internals directly
module top_module_sva;

  default clocking cb @(posedge clk); endclocking

  bit past1, past2;
  always @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // Pipeline equivalence
  a_in_prev:         assert property (past1 |-> in_prev == $past(in));
  a_edge_eq_xor:     assert property (past1 |-> edge_detected == (in ^ $past(in)));
  a_q_reg_delay:     assert property (past1 |-> q == $past(edge_detected));
  a_q_eq_two_past:   assert property (past2 |-> q == ($past(in) ^ $past(in,2)));

  // Behavioral checks
  a_no_edge_when_stable:  assert property (past1 && (in == $past(in)) |-> edge_detected == 8'h00);
  a_edge_when_change:     assert property (past1 && (in != $past(in)) |-> edge_detected != 8'h00);

  // Combinational integrity of q_reg
  always @* if (!$isunknown(edge_detected) && !$isunknown(q_reg)) begin
    assert (q_reg == edge_detected);
  end

  // No X on output once pipeline filled
  a_no_x_q: assert property (past2 |-> !$isunknown(q));

  // Coverage
  c_single_bit_toggle: cover property (past1 && $onehot(in ^ $past(in)));
  c_edge_all_ones:     cover property (past1 && edge_detected == 8'hFF);
  c_q_nonzero:         cover property (past2 && q != 8'h00);
  c_q_zero:            cover property (past2 && q == 8'h00);

endmodule

bind top_module top_module_sva sva();