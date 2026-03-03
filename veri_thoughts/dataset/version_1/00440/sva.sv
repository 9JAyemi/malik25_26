// SVA for mux4to1
module mux4to1_sva (
  input  in0, in1, in2, in3,
  input  sel0, sel1,
  input  out,
  inout  VPWR, VGND, VPB, VNB
);

  default clocking cb @(*); endclocking

  wire power_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Functional correctness when all relevant signals are known
  assert property (power_good && !$isunknown({sel1,sel0,in0,in1,in2,in3}) |->
                   out == (sel1 ? (sel0 ? in0 : in1) : (sel0 ? in2 : in3)));

  // Output maps to selected input (redundant but debuggable per case)
  assert property (power_good &&  sel1 &&  sel0 && !$isunknown(in0) |->
                   out == in0);
  assert property (power_good &&  sel1 && !sel0 && !$isunknown(in1) |->
                   out == in1);
  assert property (power_good && !sel1 &&  sel0 && !$isunknown(in2) |->
                   out == in2);
  assert property (power_good && !sel1 && !sel0 && !$isunknown(in3) |->
                   out == in3);

  // Output is not X/Z unless some input/select is X/Z
  assert property (power_good && $isunknown(out) |->
                   $isunknown({sel1,sel0,in0,in1,in2,in3}));

  // Out changes only due to a data/select change (no spurious glitches)
  assert property (power_good && $changed(out) |->
                   $changed(sel0) || $changed(sel1) ||
                   $changed(in0)  || $changed(in1)  ||
                   $changed(in2)  || $changed(in3));

  // Unselected inputs do not influence output
  assert property (power_good &&  sel1 &&  sel0 &&
                   ($changed(in1) || $changed(in2) || $changed(in3)) &&
                   $stable(sel1) && $stable(sel0) && $stable(in0) |->
                   $stable(out));
  assert property (power_good &&  sel1 && !sel0 &&
                   ($changed(in0) || $changed(in2) || $changed(in3)) &&
                   $stable(sel1) && $stable(sel0) && $stable(in1) |->
                   $stable(out));
  assert property (power_good && !sel1 &&  sel0 &&
                   ($changed(in0) || $changed(in1) || $changed(in3)) &&
                   $stable(sel1) && $stable(sel0) && $stable(in2) |->
                   $stable(out));
  assert property (power_good && !sel1 && !sel0 &&
                   ($changed(in0) || $changed(in1) || $changed(in2)) &&
                   $stable(sel1) && $stable(sel0) && $stable(in3) |->
                   $stable(out));

  // Coverage: each select combination seen
  cover property (power_good &&  sel1 &&  sel0);
  cover property (power_good &&  sel1 && !sel0);
  cover property (power_good && !sel1 &&  sel0);
  cover property (power_good && !sel1 && !sel0);

  // Coverage: propagation when selected input toggles
  cover property (power_good &&  sel1 &&  sel0 ##1 $changed(in0) && $stable(sel1) && $stable(sel0) ##0 out==in0);
  cover property (power_good &&  sel1 && !sel0 ##1 $changed(in1) && $stable(sel1) && $stable(sel0) ##0 out==in1);
  cover property (power_good && !sel1 &&  sel0 ##1 $changed(in2) && $stable(sel1) && $stable(sel0) ##0 out==in2);
  cover property (power_good && !sel1 && !sel0 ##1 $changed(in3) && $stable(sel1) && $stable(sel0) ##0 out==in3);

endmodule

bind mux4to1 mux4to1_sva mux4to1_sva_i (.*);