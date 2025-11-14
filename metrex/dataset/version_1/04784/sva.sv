// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (!$isunknown(q));

  // While reset is low, output must be 0
  assert property (!rst |-> q == 4'h0);

  // Normal increment when reset was high last cycle and is high now
  assert property (rst && $past(rst) |-> q == $past(q) + 4'd1);

  // First cycle after reset release: increment from 0 to 1
  assert property (rst && !$past(rst) |-> ($past(q) == 4'h0) && (q == $past(q) + 4'd1));

  // Coverage: reset activity
  cover property (@(negedge rst) 1);
  cover property (@(posedge rst) 1);

  // Coverage: wrap-around from 0xF to 0x0
  cover property (rst && $past(rst) && ($past(q) == 4'hF) && (q == 4'h0));

  // Coverage: generic increment step under reset deasserted
  cover property (rst && $past(rst) && (q == $past(q) + 4'd1));
endmodule

bind binary_counter binary_counter_sva sva_i (.*);