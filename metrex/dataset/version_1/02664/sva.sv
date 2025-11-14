// SVA for adder and top_module
// Focused, high-quality checks and meaningful coverage

// Assertions bound to adder
module adder_sva #(parameter W=8) (
  input logic              clk,
  input logic              reset,
  input logic [W-1:0]      a,
  input logic [W-1:0]      b,
  input logic [W-1:0]      sum
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: synchronous clear to 0 next cycle, and hold at 0 while held
  assert property (reset |=> sum == '0);
  assert property (reset && $past(reset) |-> sum == '0);

  // Functional: 1-cycle latency truncated add when not in reset
  assert property (disable iff (reset) sum == ( $past(a) + $past(b) )[W-1:0]);

  // X/Z checks on used signals in normal operation
  assert property (disable iff (reset) !$isunknown({a,b}));
  assert property (disable iff (reset) !$isunknown(sum));

  // Coverage: see both carry and no-carry cases, and reset activity
  cover property (reset ##1 !reset); // reset deassert
  cover property (!reset && !$past(reset) && (( $past(a)+$past(b) )[W] == 1'b0)
                  ##0 sum == ( $past(a)+$past(b) )[W-1:0]); // no carry
  cover property (!reset && !$past(reset) && (( $past(a)+$past(b) )[W] == 1'b1)
                  ##0 sum == ( $past(a)+$past(b) )[W-1:0]); // with carry (wrap)
endmodule

bind adder adder_sva #(.W(8)) adder_sva_i (.*);

// Assertions bound to top_module
module top_module_sva #(parameter W=8) (
  input  logic             clk,
  input  logic             reset,
  input  logic [W-1:0]     a,
  input  logic [W-1:0]     b,
  input  logic             select,
  input  logic [W-1:0]     sum,
  input  logic [W-1:0]     sum1,
  input  logic [W-1:0]     sum2
);
  default clocking cb @(posedge clk); endclocking

  // Two identical adders should always match
  assert property (sum1 == sum2);

  // Mux correctness (sampled each cycle)
  assert property (sum == (select ? sum2 : sum1));

  // Top-level sum clears next cycle on reset (both adders drive 0)
  assert property (reset |=> sum == '0);

  // X/Z checks
  assert property (!$isunknown({select}));
  assert property (!$isunknown({sum1,sum2,sum}));

  // Coverage: select both paths and toggle
  cover property (!reset && (select == 1'b0) ##1 !reset && (select == 1'b1));
  cover property (!reset && (select == 1'b1) ##1 !reset && (select == 1'b0));
endmodule

bind top_module top_module_sva #(.W(8)) top_module_sva_i (.*);