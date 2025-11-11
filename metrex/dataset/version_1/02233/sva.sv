// SVA for top_module
// Bind this file to the DUT to check functionality and provide concise coverage.

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [15:0] in,
  input logic [7:0]  out_sum,
  input logic [7:0]  upper_out,
  input logic [7:0]  lower_out,
  input logic [3:0]  counter,
  input logic [7:0]  sum
);
  default clocking cb @ (posedge clk); endclocking

  // Combinational split correctness
  a_split:    assert property (upper_out == in[15:8] && lower_out == in[7:0]);

  // Combinational adder correctness (explicit truncation to 8b)
  a_sum_comb: assert property (sum == (upper_out + lower_out + counter)[7:0]);

  // Counter behavior
  a_cnt_reset: assert property (reset |-> counter == 4'h0);
  a_cnt_incr:  assert property (!reset && $past(!reset) && $past(counter) != 4'hF |-> counter == $past(counter) + 1);
  a_cnt_wrap:  assert property (!reset && $past(!reset) && $past(counter) == 4'hF |-> counter == 4'h0);
  a_cnt_range: assert property (counter inside {[4'h0:4'hF]});

  // Registered output behavior
  a_out_reset: assert property (reset |-> out_sum == 8'h00);
  // Out equals previous-cycle truncated sum (guard past reset)
  a_out_match: assert property (!reset && !$past(reset)
                                |-> out_sum == (($past(in[15:8]) + $past(in[7:0]) + $past(counter))[7:0]));

  // Coverage
  c_reset_cycle:  cover property (reset ##1 !reset);
  c_cnt_wrap:     cover property ($past(!reset) && $past(counter)==4'hF && counter==4'h0);
  c_overflow:     cover property (!$past(reset) &&
                                  ((($past(in[15:8]) + $past(in[7:0]) + $past(counter)) >> 8) != 0));
endmodule

// Bind into DUT (accessing internals by name in the bound scope)
bind top_module top_module_sva sva_top (
  .clk(clk),
  .reset(reset),
  .in(in),
  .out_sum(out_sum),
  .upper_out(upper_out),
  .lower_out(lower_out),
  .counter(counter),
  .sum(sum)
);