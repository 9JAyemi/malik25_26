// SVA for delay_module
// Notes:
// - Checks implemented behavior (incl. double-NBA overwrite on delay_counter).
// - Covers all key branches and wrap-around.
// - Bind into DUT to observe internal delay_counter.

module delay_module_sva (
  input logic        clk,
  input logic        input_signal,
  input logic [1:0]  delay_amount,
  input logic        output_signal,
  input logic [3:0]  delay_counter
);
  default clocking cb @(posedge clk); endclocking

  // Avoid first-cycle $past issues
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Counter next-state must be previous - 1 (4-bit wrap-around)
  assert property (past_valid |-> delay_counter == $past(delay_counter) - 4'd1);

  // Explicitly check wrap-around from 0 -> 15
  assert property (past_valid && $past(delay_counter)==4'd0 |-> delay_counter==4'd15);

  // Output behavior vs previous counter value
  assert property (past_valid && $past(delay_counter) > 4'd1 |-> output_signal == 1'b0);
  assert property (past_valid && $past(delay_counter) == 4'd1 |-> output_signal == $past(input_signal));
  assert property (past_valid && $past(delay_counter) == 4'd0 |-> output_signal == $past(output_signal));

  // Output must never be 1 when previous counter > 1
  assert property (past_valid && $past(delay_counter) > 4'd1 |-> output_signal == 1'b0);

  // Coverage: exercise all branches and wrap
  cover property (past_valid && $past(delay_counter) == 4'd1 && output_signal == $past(input_signal));
  cover property (past_valid && $past(delay_counter) > 4'd1 && output_signal == 1'b0);
  cover property (past_valid && $past(delay_counter) == 4'd0 && output_signal == $past(output_signal));
  cover property (past_valid && $past(delay_counter) == 4'd0 ##1 delay_counter == 4'd15);

  // Coverage: see all delay_amount encodings (even though they don't affect counter next-state here)
  cover property (delay_amount == 2'd0);
  cover property (delay_amount == 2'd1);
  cover property (delay_amount == 2'd2);
  cover property (delay_amount == 2'd3);

  // Data path cover: input drives output only on counter==1
  cover property (past_valid && $past(delay_counter)==4'd1 && $rose(input_signal) ##1 output_signal);
  cover property (past_valid && $past(delay_counter)==4'd1 && $fell(input_signal) ##1 !output_signal);
endmodule

// Bind example (place in a testbench or a separate bind file):
// bind delay_module delay_module_sva sva_i (.*);