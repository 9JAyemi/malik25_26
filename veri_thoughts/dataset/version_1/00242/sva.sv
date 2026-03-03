// SVA checker for input_buffer
module input_buffer_sva (
  input logic in,
  input logic en,
  input logic out,
  input logic stored_out
);

  // Sample on edges of en and in
  default clocking cb @(posedge en or negedge en or posedge in or negedge in); endclocking

  // Track value of in captured on enable rise
  logic last_in_on_en_rise;
  bit   seen_rise;
  initial seen_rise = 1'b0;
  always @(posedge en) begin
    last_in_on_en_rise <= in;
    seen_rise          <= 1'b1;
  end

  // Assertions

  // When enabled, output must be transparent to input
  a_transparent: assert property (en |-> (out == in));

  // When disabled, output must not change on input changes
  a_hold_on_in_change: assert property ((!en && $changed(in)) |-> $stable(out));

  // On enable rising edge, stored_out must capture input (after NBA -> use ##0)
  a_capture_on_rise: assert property (@(posedge en) ##0 (stored_out == in));

  // On enable falling edge, output must equal last captured value (after mux settles -> use ##0)
  a_out_on_fall_matches_captured: assert property (@(negedge en) disable iff (!seen_rise) ##0 (out == last_in_on_en_rise));

  // Coverage

  c_en_rise:  cover property (@(posedge en) 1);
  c_en_fall:  cover property (@(negedge en) 1);

  // See transparent behavior while enabled
  c_in_toggle_when_enabled:  cover property (@(posedge in or negedge in) (en && $changed(out)));

  // See hold behavior while disabled
  c_in_toggle_when_disabled: cover property (@(posedge in or negedge in) (!en && $stable(out)));

  // See stored value reused on disable
  c_store_reuse: cover property (@(negedge en) disable iff (!seen_rise) ##0 (out == last_in_on_en_rise));

endmodule

// Bind to DUT
bind input_buffer input_buffer_sva u_input_buffer_sva (
  .in(in),
  .en(en),
  .out(out),
  .stored_out(stored_out)
);