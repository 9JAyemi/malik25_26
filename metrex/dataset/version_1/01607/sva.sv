// SVA for transition_capture: concise, high-quality checks and useful coverage
module tc_sva (
  input logic        clk,
  input logic        reset,
  input logic [31:0] in,
  input logic [31:0] out,
  input logic [31:0] prev_state
);
  default clocking cb @(posedge clk); endclocking

  // Guard for $past usage (handles sim start and post-reset)
  logic past_valid;
  always_ff @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Reset behavior
  a_reset_clears: assert property (reset |-> (out == 32'h0 && prev_state == 32'h0));

  // State update: prev_state captures input each cycle when not in reset
  a_state_update: assert property (past_valid && !reset |-> prev_state == $past(in));

  // Functional spec (port-level): out flags 1->0 transitions of in (vector-wise)
  a_out_spec_ports: assert property (past_valid && !reset && !$past(reset)
                                     |-> out == ($past(in) & ~in));

  // Implementation consistency (internal): out computed from prev_state and current in
  a_out_spec_internal: assert property (past_valid && !reset |-> out == ($past(prev_state) & ~in));

  // No same-bit pulse in consecutive cycles
  a_no_repeat_pulse: assert property (past_valid && !reset |-> (out & $past(out)) == 32'h0);

  // Sanity: outputs known when not in reset
  a_no_x_out: assert property (!reset |-> !$isunknown(out));

  // Coverage: observe at least one falling-edge pulse
  c_fall_pulse: cover property (past_valid && !reset && !$past(reset) &&
                                (|($past(in) & ~in)) &&
                                (out == ($past(in) & ~in)));

  // Coverage: multiple bits fall in same cycle
  c_multi_bit_fall: cover property (past_valid && !reset && !$past(reset) &&
                                    ($countones($past(in) & ~in) >= 2));

  // Coverage: reset release followed by a clean first functional cycle (no spurious out)
  c_reset_release_clean: cover property ($rose(!reset) ##1 (!reset && out == 32'h0));
endmodule

// Bind into DUT (accessing internal prev_state)
bind transition_capture tc_sva tc_sva_i (
  .clk       (clk),
  .reset     (reset),
  .in        (in),
  .out       (out),
  .prev_state(prev_state)
);