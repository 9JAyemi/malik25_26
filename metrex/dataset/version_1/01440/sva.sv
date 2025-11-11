// SystemVerilog Assertions for the provided design
// Concise, high-quality checks with focused coverage

// ---------------- dff_reset ----------------
module dff_reset_sva (input clk, input reset, input [7:0] d, input [7:0] q);
  // Async reset clears immediately (account for NBA with ##0)
  ap_dff_async_clear: assert property (@(posedge clk or posedge reset) reset |-> ##0 (q == 8'h00));
  // While reset is high at clk edge, output stays 0
  ap_dff_hold_in_reset: assert property (@(posedge clk) reset |-> (q == 8'h00));
  // When not in reset on consecutive cycles, capture d on clk
  ap_dff_capture: assert property (@(posedge clk) !reset && $past(!reset) |-> q == $past(d));
  // Coverage: see both reset assertion and a data capture
  cp_dff_reset_edge: cover property (@(posedge reset) 1);
  cp_dff_sample:     cover property (@(posedge clk) !reset && $past(!reset) && (q != $past(q)));
endmodule

bind dff_reset dff_reset_sva (.clk(clk), .reset(reset), .d(d), .q(q));

// ---------------- counter ----------------
module counter_sva (input clk, input reset, input [2:0] count);
  // Async reset clears immediately (account for NBA with ##0)
  ap_cnt_async_clear: assert property (@(posedge clk or posedge reset) reset |-> ##0 (count == 3'd0));
  // Increment when not wrapping
  ap_cnt_inc:  assert property (@(posedge clk) !reset && $past(!reset) && ($past(count) != 3'd7) |-> count == $past(count) + 3'd1);
  // Wrap 7 -> 0
  ap_cnt_wrap: assert property (@(posedge clk) !reset && $past(!reset) && ($past(count) == 3'd7)   |-> count == 3'd0);
  // Count never X/Z at clk edges
  ap_cnt_no_x: assert property (@(posedge clk) !$isunknown(count));
  // Coverage: full cycle 0..7..0
  cp_cnt_full_cycle: cover property (@(posedge clk) disable iff (reset)
                                     count==3'd0 ##1 count==3'd1 ##1 count==3'd2 ##1 count==3'd3 ##
                                     1 count==3'd4 ##1 count==3'd5 ##1 count==3'd6 ##1 count==3'd7 ##1 count==3'd0);
endmodule

bind counter counter_sva (.clk(clk), .reset(reset), .count(count));

// ---------------- and_module ----------------
// Use input-change clocking to validate pure combinational behavior
module and_module_sva (input [7:0] d, input [2:0] count, input [7:0] q);
  // Functional equivalence with the RTL expression
  ap_and_func: assert property (@(d or count) q == (d & {3{count[2]}} & {3{count[1]}} & {3{count[0]}}));
  // Upper bits are always zero due to zero-extension of 3-bit masks
  ap_and_upper_zero: assert property (@(d or count) q[7:3] == 5'b0);
  // When all count bits are 1, low bits reflect d[2:0]
  ap_and_gate_when_111: assert property (@(d or count) (&count) |-> q[2:0] == d[2:0]);
  // When any count bit is 0, low bits are forced low
  ap_and_gate_when_not_111: assert property (@(d or count) !(&count) |-> q[2:0] == 3'b000);
  // Coverage: observe gating on and off
  cp_and_on:  cover property (@(d or count) (&count) && (|d[2:0]) && (|q[2:0]));
  cp_and_off: cover property (@(d or count) !(&count));
endmodule

bind and_module and_module_sva (.d(d), .count(count), .q(q));

// ---------------- top_module (integration) ----------------
module top_module_sva (
  input clk, input reset,
  input [7:0] d, input [7:0] q,
  input [2:0] count, input [7:0] dff_out
);
  // dff_out is held at zero whenever counter MSB is 1 (since used as async reset)
  ap_top_dff_out_reset: assert property (@(posedge clk) count[2] |-> dff_out == 8'h00);
  // dff_out captures d when not reset by count[2]
  ap_top_dff_out_capture: assert property (@(posedge clk) !count[2] && $past(!count[2]) |-> dff_out == $past(d));
  // Due to the specific and_module implementation and dff reset wiring, q is always zero
  ap_top_q_always_zero: assert property (@(posedge clk) q == 8'h00);
  // Coverage: see counter MSB toggle both ways
  cp_top_msb_edges: cover property (@(posedge clk) disable iff (reset) $rose(count[2]) ##[1:$] $fell(count[2]));
endmodule

bind top_module top_module_sva (.clk(clk), .reset(reset), .d(d), .q(q), .count(count), .dff_out(dff_out));