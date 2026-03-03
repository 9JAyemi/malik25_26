// SVA checker for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  a_reset_clears:     assert property (reset |=> out == 4'h0);
  a_reset_held_zero:  assert property ($past(reset) && reset |-> out == 4'h0);

  // Functional behavior
  a_hold_when_disabled: assert property (
    !$past(reset) && !$past(enable) |=> out == $past(out)
  );

  a_inc_when_enabled: assert property (
    !$past(reset) && $past(enable) |=> out == (($past(out) + 4'd1) & 4'hF)
  );

  // No unintended changes (excluding reset-driven change)
  a_change_only_on_enable: assert property (
    !$past(reset) && $changed(out) |-> $past(enable)
  );

  // Known-value check once counter has been controlled (after reset or an enable)
  a_out_known_after_activity: assert property (
    ($past(reset) || $past(enable)) |-> !$isunknown(out)
  );

  // Coverage
  c_reset_pulse:        cover property ($rose(reset));
  c_reset_release:      cover property ($fell(reset));
  c_hold_cycle:         cover property (!$past(reset) && !$past(enable) |=> out == $past(out));
  c_inc_cycle:          cover property (!$past(reset) && $past(enable) |=> out == (($past(out) + 4'd1) & 4'hF));
  c_wraparound:         cover property (
                          !$past(reset) && $past(enable) && $past(out) == 4'hF |=> out == 4'h0
                        );
endmodule

// Bind into DUT
bind binary_counter binary_counter_sva i_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .out(out)
);