// SVA for top_module: concise, high-quality checks and coverage
// Bind into the DUT to access internals (last_in, xor_out)
module top_module_sva (
  input        clk,
  input        reset,
  input  [7:0] in,
  input  [7:0] anyedge,
  input  [7:0] final_out,
  input  [7:0] last_in,
  input  [7:0] xor_out
);

  // Reset behavior
  assert property (@(posedge clk) reset |-> (last_in == 8'h00 && anyedge == 8'h00 && final_out == in));

  // Combinational correctness of xor_out (structural)
  assert property (@(posedge clk) xor_out == (in ^ last_in));

  // Running behavior (not in reset): last_in samples in; anyedge detects any edge
  assert property (@(posedge clk) (!reset && !$past(reset)) |-> last_in == $past(in));
  assert property (@(posedge clk) (!reset && !$past(reset)) |-> anyedge == (in ^ $past(in)));

  // First cycle after reset deassertion
  assert property (@(posedge clk) $fell(reset) |-> (last_in == in && anyedge == in && xor_out == 8'h00 && final_out == in));

  // When running, xor_out collapses to zero (since last_in == in after update)
  assert property (@(posedge clk) !reset |-> xor_out == 8'h00);

  // final_out equivalence when running (xor_out is zero after flops update)
  assert property (@(posedge clk) !reset |-> final_out == anyedge);

  // No spurious edges reported when input is stable
  assert property (@(posedge clk) (!reset && !$past(reset) && (in == $past(in))) |-> (anyedge == 8'h00));

  // X-propagation hygiene (only flag if input is known)
  assert property (@(posedge clk) (!$isunknown(in)) |-> (!$isunknown({xor_out, final_out})));
  assert property (@(posedge clk) disable iff (reset) !$isunknown({last_in, anyedge}));

  // Coverage: edge scenarios
  cover property (@(posedge clk) $fell(reset));                                // reset release seen
  cover property (@(posedge clk) (!reset && $changed(in)));                    // any bit toggles
  cover property (@(posedge clk) (!reset && ((in & ~$past(in)) != 8'h00)));    // at least one rising bit
  cover property (@(posedge clk) (!reset && ((~in & $past(in)) != 8'h00)));    // at least one falling bit
  cover property (@(posedge clk) (!reset && $countones(in ^ $past(in)) >= 2)); // multi-bit toggle
  cover property (@(posedge clk) (!reset && (in == $past(in)) && anyedge==8'h00)); // stable input, no edges

endmodule

bind top_module top_module_sva sva_i (.*);