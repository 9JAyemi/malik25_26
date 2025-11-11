// SVA for the provided design. Bind to top_module.

module top_module_sva (
  input        clk,
  input        reset,
  input  [3:0] counter_out,
  input  [7:0] register_out,
  input  [7:0] final_output
);
  default clocking cb @(posedge clk); endclocking
  wire [7:0] counter_ext = {4'b0, counter_out};

  // Async resets
  ap_counter_async_reset:  assert property (@(posedge reset) counter_out   == 4'd0);
  ap_register_async_reset: assert property (@(posedge reset) register_out  == 8'd0);

  // Hold zero while reset asserted at clk edges
  ap_counter_sync_hold_zero:  assert property (reset |=> counter_out  == 4'd0);
  ap_register_sync_hold_zero: assert property (reset |=> register_out == 8'd0);

  // Counter increments by 1 (with wrap) when not in or coming from reset
  ap_counter_inc: assert property ((!reset && !$past(reset)) |=> counter_out == $past(counter_out) + 4'd1);

  // Register captures final_output on clk when not in or coming from reset
  ap_register_capture: assert property ((!reset && !$past(reset)) |=> register_out == $past(final_output));

  // Functional min correctness (with width-consistent compare/assign)
  ap_min_func: assert property (final_output == ((counter_ext < register_out) ? counter_ext : register_out));

  // No X/Z after reset
  ap_no_x: assert property (disable iff (reset) !$isunknown({counter_out, register_out, final_output}));

  // Coverage
  cv_reset:              cover property (@(posedge reset) 1'b1);
  cv_counter_wrap:       cover property ((!reset && !$past(reset) && $past(counter_out)==4'hF) |=> counter_out==4'h0);
  cv_min_branch_counter: cover property (disable iff (reset) (counter_ext <  register_out) && final_output==counter_ext);
  cv_min_branch_register:cover property (disable iff (reset) (counter_ext >= register_out) && final_output==register_out);
  cv_register_updates:   cover property (disable iff (reset) $changed(final_output) |=> register_out == $past(final_output));
endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .counter_out(counter_out),
  .register_out(register_out),
  .final_output(final_output)
);