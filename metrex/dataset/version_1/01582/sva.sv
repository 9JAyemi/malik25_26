// SVA for the provided design. Concise, high-quality checks with focused coverage.

// ----------------------- transition_detector SVA -----------------------
module transition_detector_sva (
  input clk,
  input reset,
  input [31:0] in,
  input [31:0] out
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Reference to previous input as seen by DUT (reset-aware)
  let prev_ref = $past(reset) ? 32'h0 : $past(in);

  // Reset behavior
  assert property (cb reset |-> (out == 32'h0));

  // No-change case: out holds
  assert property (cb disable iff (reset || !past_valid)
                   (in == prev_ref) |-> (out == $past(out)));

  // Change case: OR in only falling-edge bits relative to previous input
  assert property (cb disable iff (reset || !past_valid)
                   (in != prev_ref) |-> (out == ($past(out) | ((~in) & prev_ref))));

  // Monotonic/sticky: bits never clear except by reset
  assert property (cb disable iff (reset || !past_valid)
                   (($past(out) & ~out) == 32'h0));

  // New bits can only be introduced by 1->0 transitions
  assert property (cb disable iff (reset || !past_valid)
                   (((out & ~$past(out)) & ~(~in & prev_ref)) == 32'h0));

  // Coverage: observe falling transition causing new bit set
  cover property (cb disable iff (reset || !past_valid)
                  (((~in & prev_ref) & ~$past(out)) != 32'h0));

  // Coverage: observe rising-only change that does not alter out
  cover property (cb disable iff (reset || !past_valid)
                  ((in & ~prev_ref) != 32'h0 && (~in & prev_ref) == 32'h0 && out == $past(out)));
endmodule

bind transition_detector transition_detector_sva td_sva_i (
  .clk(clk), .reset(reset), .in(in), .out(out)
);

// ----------------------- shift_register SVA -----------------------
module shift_register_sva (
  input clk,
  input reset,
  input [31:0] in,
  input [31:0] q,
  input [2:0]  counter
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  assert property (cb reset |-> (q == 32'h0 && counter == 3'd0));

  // Actual RTL effect (due to width truncation): q takes in each cycle
  assert property (cb disable iff (reset || !past_valid)
                   (q == in));

  // Counter increments modulo-4
  assert property (cb disable iff (reset || !past_valid)
                   (counter == (($past(counter) == 3'd3) ? 3'd0 : $past(counter) + 3'd1)));

  // Coverage: wrap and general increment
  cover property (cb disable iff (reset || !past_valid) ($past(counter)==3'd3 && counter==3'd0));
  cover property (cb disable iff (reset || !past_valid) ($past(counter)!=3'd3 && counter==$past(counter)+3'd1));
endmodule

bind shift_register shift_register_sva sr_sva_i (
  .clk(clk), .reset(reset), .in(in), .q(q), .counter(counter)
);

// ----------------------- top_module SVA -----------------------
module top_module_sva (
  input clk,
  input reset,
  input [31:0] in,
  input [31:0] out,
  input [31:0] trans_out,
  input [31:0] shift_out
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset propagates to all outputs
  assert property (cb reset |-> (out==32'h0 && trans_out==32'h0 && shift_out==32'h0));

  // OR composition holds
  assert property (cb out == (trans_out | shift_out));

  // Given shift_register behavior, shift_out follows trans_out (non-reset)
  assert property (cb disable iff (reset || !past_valid)
                   (shift_out == trans_out));

  // Therefore, out equals trans_out when not in reset
  assert property (cb disable iff (reset || !past_valid)
                   (out == trans_out));

  // End-to-end coverage: observe a bit getting set in top out due to a 1->0 transition at input
  let prev_in = $past(reset) ? 32'h0 : $past(in);
  cover property (cb disable iff (reset || !past_valid)
                  (((~in & prev_in) & ~($past(out))) != 32'h0 && (out & ~$past(out)) != 32'h0));
endmodule

bind top_module top_module_sva top_sva_i (
  .clk(clk), .reset(reset), .in(in), .out(out),
  .trans_out(trans_out), .shift_out(shift_out)
)