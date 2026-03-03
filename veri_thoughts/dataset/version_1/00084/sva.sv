// SVA for constant_voltage_driver
// Note: vout is 1-bit; checks use vref[0] as per assignment truncation.

module constant_voltage_driver_sva (
  input logic        control,
  input logic [7:0]  vref,
  input logic        vout
);

  // Functional spec: after delta, vout == (control ? vref[0] : 1'b0)
  assert property (@(control or vref or vout)
    disable iff ($isunknown({control,vref}))
    1'b1 |-> ##0 (vout == (control ? vref[0] : 1'b0))
  ) else $error("vout must equal control ? vref[0] : 0");

  // vout can only change if control or vref[0] changes
  assert property (@(control or vref or vout)
    $changed(vout) |-> ($changed(control) or $changed(vref[0]))
  ) else $error("vout changed without control/vref[0] change");

  // Upper bits of vref must not affect vout
  assert property (@(vref)
    ($changed(vref[7:1]) && $stable(vref[0]) && $stable(control)) |-> ##0 $stable(vout)
  ) else $error("vout changed due to vref[7:1]");

  // No X/Z on vout when inputs are known
  assert property (@(control or vref or vout)
    disable iff ($isunknown({control,vref}))
    !$isunknown(vout)
  ) else $error("vout unknown with known inputs");

  // Coverage
  cover property (@(control) $rose(control));
  cover property (@(control) $fell(control));
  cover property (@(vref[0]) control && $rose(vref[0]) ##0 $rose(vout));
  cover property (@(vref[0]) control && $fell(vref[0]) ##0 $fell(vout));
  cover property (@(vref) control && $changed(vref[7:1]) && $stable(vref[0]) ##0 $stable(vout));
  cover property (@(vref[0]) !control && $changed(vref[0]) ##0 (vout==1'b0));

endmodule

bind constant_voltage_driver constant_voltage_driver_sva sva_i (
  .control(control), .vref(vref), .vout(vout)
);