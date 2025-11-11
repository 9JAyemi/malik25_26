// SVA bind file for the provided design

// Counter assertions
module sva_binary_counter_with_sync_reset (
    input logic        clk,
    input logic        reset,
    input logic [3:0]  Q
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset to zero
  a_cnt_reset: assert property (reset |-> (Q == 4'h0));

  // Step behavior (increment or wrap) each non-reset cycle
  a_cnt_step:  assert property (disable iff (reset)
                                Q == (($past(Q) == 4'hF) ? 4'h0 : ($past(Q) + 4'h1)));

  // No X/Z when not in reset
  a_cnt_known: assert property (disable iff (reset) !$isunknown(Q));

  // Cover wrap 15 -> 0
  c_cnt_wrap:  cover  property (disable iff (reset) ($past(Q) == 4'hF && Q == 4'h0));
endmodule

bind binary_counter_with_sync_reset sva_binary_counter_with_sync_reset bcnt_sva (
  .clk(clk), .reset(reset), .Q(Q)
);


// Shift-register assertions
module sva_shift_register_with_serial_in_out (
    input logic        clk,
    input logic        reset,
    input logic        SI,
    input logic        SO,
    input logic [3:0]  Q
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset clears Q; SO is not driven in RTL on reset, so must be stable
  a_sr_reset: assert property (reset |-> (Q == 4'h0 && $stable(SO)));

  // Shift behavior and SO reflects prior LSB
  a_sr_step:  assert property (disable iff (reset)
                               (Q  == { $past(Q[2:0]), $past(SI) }) &&
                               (SO == $past(Q[0])));

  // No X/Z when not in reset
  a_sr_known: assert property (disable iff (reset) !$isunknown({Q, SO}));

  // Coverage: observe a '1' being shifted out; and a recognizable internal pattern
  c_sr_so1:   cover  property (disable iff (reset) ($past(Q[0]) && SO));
  c_sr_pat:   cover  property (disable iff (reset) (Q == 4'b1010));
endmodule

bind shift_register_with_serial_in_out sva_shift_register_with_serial_in_out sreg_sva (
  .clk(clk), .reset(reset), .SI(SI), .SO(SO), .Q(Q)
);


// Top-level integration assertions
module sva_top_module (
    input logic        clk,
    input logic        reset,
    input logic [3:0]  counter_out,
    input logic [3:0]  shift_reg_out,
    input logic [3:0]  bitwise_OR_out,
    input logic [3:0]  Q
);
  default clocking cb @(posedge clk); endclocking

  // Synchronous reset to zero
  a_top_reset:   assert property (reset |-> (Q == 4'h0));

  // Q loads OR result each non-reset cycle (same-cycle capture semantics)
  a_q_loads_or:  assert property (disable iff (reset) (Q == bitwise_OR_out));

  // OR correctness at integration point
  a_or_correct:  assert property (bitwise_OR_out == (counter_out | shift_reg_out));

  // No X/Z when not in reset
  a_top_known:   assert property (disable iff (reset) !$isunknown({Q, bitwise_OR_out, counter_out, shift_reg_out}));

  // Coverage: reach all ones at top; simple post-reset data flow
  c_top_all1:    cover  property (disable iff (reset) (Q == 4'hF));
  c_top_flow:    cover  property ($fell(reset) ##[1:32] (Q == 4'h0) ##1 (Q == bitwise_OR_out));
endmodule

bind top_module sva_top_module top_sva (
  .clk(clk), .reset(reset),
  .counter_out(counter_out), .shift_reg_out(shift_reg_out),
  .bitwise_OR_out(bitwise_OR_out), .Q(Q)
);