// SVA for schmitt_trigger. Bind into DUT scope to access internals.
module schmitt_trigger_sva;

  // Use DUT clock
  default clocking cb @(posedge clk); endclocking

  // Avoid $past unknown on first cycle
  logic initdone;
  initial initdone = 0;
  always @(posedge clk) initdone <= 1;

  // Basic parameter sanity (window must be ordered)
  initial begin
    assert (vth + hysteresis > vtl - hysteresis)
      else $error("schmitt_trigger: invalid thresholds: vth+hysteresis <= vtl-hysteresis");
  end

  // X/Z guards
  assert property (disable iff (!initdone) !$isunknown(in));
  assert property (disable iff (!initdone) !$isunknown(out));

  // Combinational mirror
  assert property (disable iff (!initdone) out == out_reg);

  // prev_in tracks input each cycle
  assert property (disable iff (!initdone) prev_in == $past(in));

  // Thresholds cause updates (registered effect)
  assert property (disable iff (!initdone) (in > (vth + hysteresis)) |=> out_reg == 1'b1);
  assert property (disable iff (!initdone) (in < (vtl - hysteresis)) |=> out_reg == 1'b0);

  // No spurious toggles: output changes only if threshold condition held in prior cycle
  assert property (disable iff (!initdone) $rose(out_reg) |-> $past(in > (vth + hysteresis)));
  assert property (disable iff (!initdone) $fell(out_reg) |-> $past(in < (vtl - hysteresis)));

  // Hold behavior when in the hysteresis band
  assert property (disable iff (!initdone)
                   !((in > (vth + hysteresis)) || (in < (vtl - hysteresis)))
                   |=> out_reg == $past(out_reg));

  // Monotonic with hysteresis (stickiness) until opposite threshold is crossed
  assert property (disable iff (!initdone) (out_reg == 1) |-> (out_reg == 1 until (in < (vtl - hysteresis))));
  assert property (disable iff (!initdone) (out_reg == 0) |-> (out_reg == 0 until (in > (vth + hysteresis))));

  // Coverage: exercise both thresholds and round-trip
  cover property (disable iff (!initdone) (in > (vth + hysteresis)) ##1 out_reg == 1);
  cover property (disable iff (!initdone) (in < (vtl - hysteresis)) ##1 out_reg == 0);
  cover property (disable iff (!initdone)
                  (in > (vth + hysteresis)) ##1 out_reg == 1
                  ##[1:10] (in < (vtl - hysteresis)) ##1 out_reg == 0);

  // Coverage: prev_in tracking a change
  cover property (disable iff (!initdone) $changed(in) ##1 prev_in == $past(in));

endmodule

bind schmitt_trigger schmitt_trigger_sva st_sva();