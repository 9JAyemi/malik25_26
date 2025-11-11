// SystemVerilog Assertions for the provided design
// Focused, high-quality checks with concise coverage.
// Bind modules to keep DUT untouched.

// xor_flipflop SVA
module xor_flipflop_sva (
  input clk,
  input a,
  input b,
  input q,
  input xor_out
);
  bit saw_pos;
  initial saw_pos = 0;
  always @(posedge clk) saw_pos <= 1;

  // Functional correctness
  ap_xor_func:   assert property (@(posedge clk) q == (a ^ b));
  ap_xor_comb:   assert property (@(posedge clk) xor_out == (a ^ b));

  // Knownness when inputs are known at sample
  ap_xor_no_x:   assert property (@(posedge clk) (!$isunknown({a,b})) |-> !$isunknown(q));

  // Coverage
  cp_xor0:       cover property (@(posedge clk) (a ^ b) == 1'b0);
  cp_xor1:       cover property (@(posedge clk) (a ^ b) == 1'b1);
  cp_xor_toggle: cover property (@(posedge clk) (a ^ b) != $past(a ^ b));
endmodule

bind xor_flipflop xor_flipflop_sva xor_flipflop_sva_i (
  .clk(clk), .a(a), .b(b), .q(q), .xor_out(xor_out)
);


// dual_edge_ff SVA
module dual_edge_ff_sva (
  input clk,
  input d,
  input q,
  input q1,
  input q2
);
  bit saw_pos, saw_neg;
  initial begin saw_pos = 0; saw_neg = 0; end
  always @(posedge clk) saw_pos <= 1;
  always @(negedge clk) saw_neg <= 1;

  // Stage transfers
  ap_q1_cap:    assert property (@(negedge clk) disable iff (!saw_pos)
                                 q1 == $past(d, 1, posedge clk));
  ap_q2_cap:    assert property (@(negedge clk) disable iff (!saw_pos)
                                 q2 == $past(q1, 1, posedge clk));
  ap_q_cap:     assert property (@(posedge clk) disable iff (!saw_neg)
                                 q  == $past(q2, 1, negedge clk));

  // End-to-end: d at posedge -> q next posedge
  ap_d2q_1cyc:  assert property (@(posedge clk) disable iff (!saw_pos)
                                 q == $past(d, 1, posedge clk));

  // Knownness propagation
  ap_no_x:      assert property (@(posedge clk) disable iff (!saw_pos)
                                 !$isunknown($past(d, 1, posedge clk)) |-> !$isunknown(q));

  // Coverage
  cp_q_toggle:  cover property (@(posedge clk) q != $past(q));
  cp_q0:        cover property (@(posedge clk) q == 1'b0);
  cp_q1:        cover property (@(posedge clk) q == 1'b1);
endmodule

bind dual_edge_ff dual_edge_ff_sva dual_edge_ff_sva_i (
  .clk(clk), .d(d), .q(q), .q1(q1), .q2(q2)
);


// combined_module SVA
module combined_module_sva (
  input clk,
  input a,
  input b,
  input q,
  input xor_out,
  input dual_edge_out
);
  bit saw_pos;
  initial saw_pos = 0;
  always @(posedge clk) saw_pos <= 1;

  // End-to-end function: q equals (a^b) delayed by one posedge
  ap_end2end:   assert property (@(posedge clk) disable iff (!saw_pos)
                                 q == $past(a ^ b, 1, posedge clk));

  // Pipeline step and connectivity
  ap_stage:     assert property (@(posedge clk) disable iff (!saw_pos)
                                 dual_edge_out == $past(xor_out, 1, posedge clk));
  ap_conn:      assert property (@(posedge clk) q == dual_edge_out);

  // Coverage
  cp_q_toggle:  cover property (@(posedge clk) q != $past(q));
endmodule

bind combined_module combined_module_sva combined_module_sva_i (
  .clk(clk), .a(a), .b(b), .q(q), .xor_out(xor_out), .dual_edge_out(dual_edge_out)
);


// top_module SVA
module top_module_sva (
  input clk,
  input a,
  input b,
  input q
);
  bit saw_pos;
  initial saw_pos = 0;
  always @(posedge clk) saw_pos <= 1;

  // Top-level end-to-end check
  ap_top_end2end: assert property (@(posedge clk) disable iff (!saw_pos)
                                   q == $past(a ^ b, 1, posedge clk));

  // Coverage
  cp_top_toggle:  cover property (@(posedge clk) q != $past(q));
  cp_top_q0:      cover property (@(posedge clk) q == 1'b0);
  cp_top_q1:      cover property (@(posedge clk) q == 1'b1);
endmodule

bind top_module top_module_sva top_module_sva_i (
  .clk(clk), .a(a), .b(b), .q(q)
);