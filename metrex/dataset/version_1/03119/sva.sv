// SVA for mux4to1
module mux4to1_sva(input [3:0] out, input [3:0] in0, input [3:0] in1, input [1:0] sel);

  // Sample on any relevant combinational change
  default clocking cb @(in0 or in1 or sel); endclocking

  // Functional correctness (matches actual RTL behavior)
  assert property (disable iff ($isunknown({sel,in0,in1})))
    out == (sel[0] ? in1 : in0);

  // MSB of sel is redundant (should not affect out)
  assert property (disable iff ($isunknown({sel,in0,in1})))
    $changed(sel[1]) |-> $stable(out);

  // Out must not go X/Z when inputs and sel are known
  assert property (disable iff ($isunknown({sel,in0,in1})))
    !$isunknown(out);

  // Coverage: see all select combinations and corresponding output
  cover property (disable iff ($isunknown({sel,in0,in1})))
    (sel==2'b00 && out==in0);
  cover property (disable iff ($isunknown({sel,in0,in1})))
    (sel==2'b01 && out==in1);
  cover property (disable iff ($isunknown({sel,in0,in1})))
    (sel==2'b10 && out==in0);
  cover property (disable iff ($isunknown({sel,in0,in1})))
    (sel==2'b11 && out==in1);

  // Coverage: switching selected source changes output immediately
  cover property (disable iff ($isunknown({sel,in0,in1})))
    $rose(sel[0]) ##0 (out==in1);
  cover property (disable iff ($isunknown({sel,in0,in1})))
    $fell(sel[0]) ##0 (out==in0);

  // Coverage: sel[1] toggles without affecting out
  cover property (disable iff ($isunknown({sel,in0,in1})))
    $changed(sel[1]) && $stable(out);

endmodule

// Bind into DUT
bind mux4to1 mux4to1_sva i_mux4to1_sva(.out(out), .in0(in0), .in1(in1), .sel(sel));