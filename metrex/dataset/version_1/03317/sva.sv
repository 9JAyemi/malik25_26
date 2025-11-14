// SVA for fsm_4bit_binary_counter
// Bind into all instances of the DUT
bind fsm_4bit_binary_counter fsm_4bit_binary_counter_sva sva_i (.*);

module fsm_4bit_binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count,
  input logic [1:0]  state
);

  default clocking cb @(posedge clk); endclocking

  // Async reset drives state/count to 0 immediately
  assert property (@(posedge reset) state==2'b00 && count==4'b0000);

  // While reset is asserted, state/count remain 0
  assert property (@(posedge clk) reset |-> ((state==2'b00 && count==4'b0000) throughout reset));

  // State must increment modulo-4 each cycle (skip check if reset disturbed history)
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown($past(state,1,reset)) |-> state == $past(state,1,reset) + 2'b01);

  // Count must increment modulo-16 each cycle (skip check if reset disturbed history)
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown($past(count,1,reset)) |-> count == $past(count,1,reset) + 4'd1);

  // First tick after leaving reset: state=1, count=1
  assert property (@(posedge clk) $past(reset) && !reset |-> state==2'b01 && count==4'd1);

  // No unknowns after reset is low
  assert property (@(posedge clk) disable iff (reset) state inside {2'b00,2'b01,2'b10,2'b11});
  assert property (@(posedge clk) disable iff (reset) !$isunknown(count));

  // Coverage: full state cycle 00->01->10->11->00 without reset
  cover property (@(posedge clk) disable iff (reset)
                  state==2'b00 ##1 state==2'b01 ##1 state==2'b10 ##1 state==2'b11 ##1 state==2'b00);

  // Coverage: count wrap 15->0
  cover property (@(posedge clk) disable iff (reset)
                  $past(count,1,reset)==4'd15 && count==4'd0);

  // Coverage: 16-cycle count period without reset
  cover property (@(posedge clk) disable iff (reset) count==4'd0 ##16 count==4'd0);

  // Coverage: reset asserted at least once
  cover property (@(posedge reset) 1'b1);

endmodule