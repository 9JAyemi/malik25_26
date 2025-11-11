// SVA for the provided design. Bind these modules to the DUT.

////////////////////////////////////////////////////////////////////////////////
// binary_counter assertions
module binary_counter_sva(input logic clk, input logic reset, input logic [3:0] count);
  default clocking cb @(posedge clk); endclocking
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  a_cnt_reset_now_zero: assert property (reset |=> count == 4'd0);
  a_cnt_hold_in_reset:  assert property (reset && $past(reset) |-> count == 4'd0);

  // Increment-by-1 modulo-16 when not in reset
  a_cnt_inc: assert property (past_valid && !reset |-> count == ($past(count) + 4'd1));

  // No X/Z on count
  a_cnt_no_x: assert property (!$isunknown(count));

  // Coverage
  c_cnt_wrap:  cover property (!reset && count == 4'hF ##1 !reset && count == 4'h0);
  c_cnt_reset_release: cover property (reset ##1 !reset);
endmodule

bind binary_counter binary_counter_sva(.clk(clk), .reset(reset), .count(count));

////////////////////////////////////////////////////////////////////////////////
// register assertions
module register_sva(input logic clk, input logic reset, input logic [7:0] d, input logic [7:0] q);
  default clocking cb @(posedge clk); endclocking
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  a_reg_reset_now_val: assert property (reset |=> q == 8'h34);
  a_reg_hold_in_reset: assert property (reset && $past(reset) |-> q == 8'h34);

  // Sample D on each clock when not in reset
  a_reg_sample: assert property (past_valid && !reset |-> q == $past(d));

  // No X/Z on q
  a_reg_no_x: assert property (!$isunknown(q));

  // Coverage
  c_reg_sample_change: cover property (past_valid && !reset && $past(!reset) && q != $past(q));
  c_reg_reset_release: cover property (reset ##1 !reset);
endmodule

bind register register_sva(.clk(clk), .reset(reset), .d(d), .q(q));

////////////////////////////////////////////////////////////////////////////////
// top-level/control mux assertions (also checks zero-extension of counter)
module top_module_sva(
  input logic clk, input logic reset, input logic select,
  input logic [7:0] q, input logic [7:0] reg_out, input logic [3:0] counter_out
);
  default clocking cb @(posedge clk); endclocking
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // Mux correctness
  a_mux_sel_reg: assert property (select  |-> q == reg_out);
  a_mux_sel_cnt: assert property (!select |-> (q[7:4] == 4'b0 && q[3:0] == counter_out));

  // Reset effect at top (next cycle due to synchronous reset)
  a_top_reset_reg_path: assert property (reset && select  |=> q == 8'h34);
  a_top_reset_cnt_path: assert property (reset && !select |=> q == 8'h00);

  // No X/Z on top output
  a_top_q_no_x: assert property (!$isunknown(q));

  // Coverage: exercise both mux paths
  c_mux_both_paths: cover property (select ##1 !select);
endmodule

bind top_module top_module_sva(
  .clk(clk), .reset(reset), .select(select),
  .q(q), .reg_out(reg_out), .counter_out(counter_out)
);