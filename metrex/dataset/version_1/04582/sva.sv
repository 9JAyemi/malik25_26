// SVA for up_counter
module up_counter_sva #(parameter int WIDTH = 3)
(
  input  logic                  clk,
  input  logic                  rst,
  input  logic [WIDTH-1:0]      count,
  input  logic [WIDTH-1:0]      reg_count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // No X/Z on key signals after init
  assert property (!$isunknown({rst, reg_count, count})) else $error("X/Z detected");

  // Output mirrors internal reg
  assert property (count == reg_count) else $error("count != reg_count");

  // Synchronous reset: next cycle is zero
  assert property (rst |=> reg_count == '0) else $error("Reset didn't drive 0 next cycle");

  // While reset held (from 2nd cycle onward), value stays zero
  assert property (rst && $past(rst) |-> reg_count == '0) else $error("Not 0 while reset held");

  // Normal increment by +1 mod 2^WIDTH when not in reset
  assert property (!rst |=> reg_count == $past(reg_count) + 1'b1) else $error("Increment failure");

  // Explicit wrap: max -> 0 on next cycle when not in reset
  assert property (!rst && reg_count == {WIDTH{1'b1}} |=> reg_count == '0) else $error("Wrap failed");

  // Coverage
  cover property (rst ##1 reg_count == '0);                         // reset drives zero
  cover property ($fell(rst) ##1 reg_count == 1);                   // first increment after release
  cover property (!rst && reg_count == {WIDTH{1'b1}} ##1 reg_count == '0); // wrap event

  // Hit all states at least once in run mode
  localparam int MAX = 1 << WIDTH;
  genvar i;
  generate
    for (i = 0; i < MAX; i++) begin : cv_states
      cover property (!rst && reg_count == i[WIDTH-1:0]);
    end
  endgenerate
endmodule

// Bind SVA to DUT (allows access to internal reg_count)
bind up_counter up_counter_sva #(.WIDTH(3)) up_counter_sva_b (
  .clk       (clk),
  .rst       (rst),
  .count     (count),
  .reg_count (reg_count)
);